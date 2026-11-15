-- Prove2me | Theorems.Thm_UniversalNonstochastic_Main_Supplement_theorem_8
-- name    : UniversalNonstochastic.Main.Supplement.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:31:14.038894+00:00
-- url     : https://prove2.me/theorems/99d0ed82-77bb-4a3c-aacd-7d8ce1600fad
-- title:
--   Theorem 8 — $2^{-\alpha-c}\le\mathbf m(N^{qu}_{\alpha,\beta})\le2^{-\alpha+K(\alpha)+c}$, and the upper bound is optimal
-- statement:
--   Let $N^{qu}_{\alpha,\beta}$ be the set of objects $\omega$ for which no elementary probability measure $Q$ has $K(Q)\le\alpha$, $Q(\{\omega\})>0$ and $K(\omega)\ge-\log Q(\{\omega\})-\beta$.
--
--   1. There is $c>0$ such that for all $\alpha\in\mathbb N_0$ and $\beta\in[0,\infty]$,
--   $$2^{-\alpha-c}\le\mathbf m(N^{qu}_{\alpha,\beta})\le2^{-\alpha+K(\alpha)+c}.\qquad(10)$$
--   2. If $f:\mathbb N_0\to\mathbb N_0$ is upper semicomputable and $\sum_n2^{-f(n)}=\infty$, then for infinitely many $\alpha$,
--   $$\mathbf m(N^{qu}_{\alpha,\beta})>2^{-\alpha+f(\alpha)}\qquad\text{for all }\beta\in[0,\infty].$$
--
--   The second part shows that the upper bound in (10), and hence the dependence on $\alpha$ of the upper bound of Theorem 7, cannot be improved.
--
--   Differences from the source:
--   - encoding: K(α) as a real exponent → ∃ κ : ℕ, K(α) = κ, and the bound with κ; reason: K(α) is valued in ℕ ∪ {∞} in Lean; for an optimal decoder it is finite, and asserting the witness avoids any default value of a conversion at ∞
--   - encoding: ∑ₙ 2^(−f(n)) = ∞ → the ℝ≥0∞ sum ∑' (1/2)^f(n) = ⊤; reason: series of nonnegative terms; no real-tsum default
-- source:
--   Vladimir Vovk, The universal measure of nonstochastic objects, STOC 2027 submission #11 (October 2026), SHA-256 1ca25c4b7c38d8f49718c9fecbc2a434a7592886b44992c4fbef31ab3f480078, Theorem 8, eq. (10), p.9 (PDF p.9)

import Mathlib
import Definitions.Def_UniversalNonstochastic_Main_Effective
import Definitions.Def_UniversalNonstochastic_Main_UniversalMeasure
import Definitions.Def_UniversalNonstochastic_Main_Complexity
import Definitions.Def_UniversalNonstochastic_Main_Supplement_Complexities
import Definitions.Def_UniversalNonstochastic_Main_Supplement_Deficiencies

open scoped ENNReal

namespace UniversalNonstochastic.Main.Supplement

/-- Theorem 8, p.9. (10): there is `c > 0` such that for all `α ∈ ℕ₀` and `β ∈ [0, ∞]`,
`2^{-α-c} ≤ m(N^{qu}_{α,β}) ≤ 2^{-α+K(α)+c}` (with `K(α)` a natural number `κ`).
Moreover, for every upper semicomputable `f : ℕ₀ → ℕ₀` with `∑ₙ 2^{-f(n)} = ∞`, for infinitely
many `α`, `m(N^{qu}_{α,β}) > 2^{-α+f(α)}` for all `β ∈ [0, ∞]`. -/
theorem theorem_8 (m : UniversalSemimeasure) (U : OptimalPrefixDecoder) :
    (∃ c : ℝ, 0 < c ∧ ∀ (α : ℕ) (β : EReal), 0 ≤ β →
      ∃ κ : ℕ, KNat U α = κ ∧
        (2 : ℝ) ^ (-(α : ℝ) - c) ≤ mass m (nonQuasiStochasticU U α β) ∧
        mass m (nonQuasiStochasticU U α β) ≤ (2 : ℝ) ^ (-(α : ℝ) + κ + c)) ∧
    ∀ f : ℕ → ℕ, IsUpperSemicomputableNat f → ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ f n = ⊤ →
      {α : ℕ | ∀ β : EReal, 0 ≤ β →
        (2 : ℝ) ^ (-(α : ℝ) + (f α : ℝ)) <
          mass m (nonQuasiStochasticU U α β)}.Infinite := by sorry

end UniversalNonstochastic.Main.Supplement
