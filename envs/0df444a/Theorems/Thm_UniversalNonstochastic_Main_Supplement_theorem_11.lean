-- Prove2me | Theorems.Thm_UniversalNonstochastic_Main_Supplement_theorem_11
-- name    : UniversalNonstochastic.Main.Supplement.theorem_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:33:26.247655+00:00
-- url     : https://prove2.me/theorems/742d0fa5-e71a-4033-9a4c-aaad55a2bd0b
-- title:
--   Theorem 11 — the summability dichotomy for $d_F$
-- statement:
--   Let $F:\mathcal X\to\mathbb N_0$ be upper semicomputable and $d_F(\omega\mid Q)=-\log Q(\{\omega\})-F(\omega)$.
--
--   1. There is $c>0$ such that for all $\alpha\in\mathbb N_0$ and $\beta\in[0,\infty)$, $\mathbf m(N_{\alpha,\beta}(d_F))\ge2^{-\alpha-c}$, and, if $\sum_\omega2^{-F(\omega)}<\infty$, also $\mathbf m(N_{\alpha,\beta}(d_F))\le2^{-\alpha+K(\alpha)+c}$. That is, under convergence,
--   $$2^{-\alpha-c}\le\mathbf m(N_{\alpha,\beta}(d_F))\le2^{-\alpha+K(\alpha)+c},\qquad(14)$$
--   and only the upper bound depends on the condition on $F$.
--   2. If $\sum_\omega2^{-F(\omega)}=\infty$, there is $c>0$ such that for all $\alpha\in\mathbb N_0$ and $\beta\in[0,\infty)$,
--   $$\tau(\max(\alpha,\beta))/c\le\mathbf m(N_{\alpha,\beta}(d_F))\le c\,\tau(\alpha)\qquad(15)$$
--   and
--   $$\bigl|-\log\mathbf m(N_{\alpha,\beta}(d_F))-\min(\alpha,\mu(\beta))\bigr|\le c\log(\alpha+2).\qquad(16)$$
--
--   Prefix and plain complexity lie on opposite sides of this dichotomy.
--
--   Differences from the source:
--   - encoding: bullet 1: if ∑ < ∞ then ∃ c with (14); (only the upper bound depends on the condition) → ∃ c, for all α, β: the lower bound of (14), and the upper bound under ∑ ≠ ⊤; reason: equivalent to the bullet together with its parenthetical: take the larger of the two constants
--   - encoding: ∑ 2^(−F(ω)) = ∞ (resp. < ∞) → the ℝ≥0∞ sum ∑' (1/2)^F(ω) = ⊤ (resp. ≠ ⊤); reason: series of nonnegative terms; no real-tsum default
--   - encoding: K(α) as a real exponent → ∃ κ : ℕ, K(α) = κ, and the bound with κ; reason: K(α) is valued in ℕ ∪ {∞} in Lean; for an optimal decoder it is finite, and asserting the witness avoids any default value of a conversion at ∞
--   - encoding: |−log m(N) − min(α, µ(β))| ≤ c log(α + 2) (16) → 2^(−min(α,µ(β)) − c log₂(α+2)) ≤ m(N) ≤ 2^(−min(α,µ(β)) + c log₂(α+2)), with min(α, µ(β)) converted by toNat; reason: equivalent for m(N) > 0, which the source's inequality forces (−log 0 = ∞); min(α, µ(β)) ≤ α is finite, so the conversion is exact
-- source:
--   Vladimir Vovk, The universal measure of nonstochastic objects, STOC 2027 submission #11 (October 2026), SHA-256 1ca25c4b7c38d8f49718c9fecbc2a434a7592886b44992c4fbef31ab3f480078, Theorem 11, eqs. (14)–(16), p.11 (PDF p.11)

import Mathlib
import Definitions.Def_UniversalNonstochastic_Main_Effective
import Definitions.Def_UniversalNonstochastic_Main_UniversalMeasure
import Definitions.Def_UniversalNonstochastic_Main_Complexity
import Definitions.Def_UniversalNonstochastic_Main_ElementaryModels
import Definitions.Def_UniversalNonstochastic_Main_Supplement_Complexities

open scoped ENNReal

namespace UniversalNonstochastic.Main.Supplement

/-- Theorem 11, p.11: let `F : 𝓧 → ℕ₀` be upper semicomputable.
* There is `c > 0` such that for all `α ∈ ℕ₀`, `β ∈ [0, ∞)`: `2^{-α-c} ≤ m(N_{α,β}(d_F))`, and,
  if `∑_ω 2^{-F(ω)} < ∞`, also `m(N_{α,β}(d_F)) ≤ 2^{-α+K(α)+c}` (14) (only the upper bound
  depends on the condition on `F`).
* If `∑_ω 2^{-F(ω)} = ∞`, there is `c > 0` such that for all `α ∈ ℕ₀`, `β ∈ [0, ∞)`:
  `τ(max(α, β))/c ≤ m(N_{α,β}(d_F)) ≤ c τ(α)` (15) and
  `|-log₂ m(N_{α,β}(d_F)) - min(α, µ(β))| ≤ c log₂(α + 2)` (16), the latter written as the
  equivalent two-sided bound on `m(N_{α,β}(d_F))`. -/
theorem theorem_11 (m : UniversalSemimeasure) (U : OptimalPrefixDecoder) (F : ℕ+ → ℕ)
    (hF : IsUpperSemicomputableNat F) :
    (∃ c : ℝ, 0 < c ∧ ∀ (α : ℕ) (β : ℝ), 0 ≤ β →
      ∃ κ : ℕ, KNat U α = κ ∧
        (2 : ℝ) ^ (-(α : ℝ) - c) ≤ mass m (nonQuasiStochastic U (dF F) α β) ∧
        (∑' ω : ℕ+, (2⁻¹ : ℝ≥0∞) ^ F ω ≠ ⊤ →
          mass m (nonQuasiStochastic U (dF F) α β) ≤ (2 : ℝ) ^ (-(α : ℝ) + κ + c))) ∧
    (∑' ω : ℕ+, (2⁻¹ : ℝ≥0∞) ^ F ω = ⊤ →
      ∃ c : ℝ, 0 < c ∧ ∀ (α : ℕ) (β : ℝ), 0 ≤ β →
        tail m (max (α : ℝ) β) / c ≤ mass m (nonQuasiStochastic U (dF F) α β) ∧
        mass m (nonQuasiStochastic U (dF F) α β) ≤ c * tail m (α : ℝ) ∧
        (2 : ℝ) ^ (-(((min (α : ℕ∞) (invBusyBeaver U β)).toNat : ℕ) : ℝ) -
            c * Real.logb 2 ((α : ℝ) + 2)) ≤ mass m (nonQuasiStochastic U (dF F) α β) ∧
        mass m (nonQuasiStochastic U (dF F) α β) ≤
          (2 : ℝ) ^ (-(((min (α : ℕ∞) (invBusyBeaver U β)).toNat : ℕ) : ℝ) +
            c * Real.logb 2 ((α : ℝ) + 2))) := by sorry

end UniversalNonstochastic.Main.Supplement
