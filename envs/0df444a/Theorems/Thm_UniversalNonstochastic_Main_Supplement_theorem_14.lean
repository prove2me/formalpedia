-- Prove2me | Theorems.Thm_UniversalNonstochastic_Main_Supplement_theorem_14
-- name    : UniversalNonstochastic.Main.Supplement.theorem_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:34:55.855413+00:00
-- url     : https://prove2.me/theorems/d2726f4f-d5bd-421e-8755-fb33b69651a4
-- title:
--   Theorem 14 — omnibus bounds (26)–(28) for nonstochastic objects
-- statement:
--   Let $F$ and $d_p$ be as in Theorem 13, and for a deficiency $d$ let $d^{\mathrm{set}}(\omega\mid Q)=d(\omega\mid Q)$ if $Q$ is the uniform measure $U_\Omega$ on a nonempty finite set $\Omega$ and $\infty$ otherwise. There is $c>0$ such that for all $\alpha\in\mathbb N_0$, all $\beta\in[0,\infty)$ and each $d\in\{d_e,d_p,d_K,d_F\}$,
--   $$\mathbf m(N_{\alpha,\beta}(d^{\mathrm{set}}))\ge\bigl(2^{-\alpha}+\tau(\max(\alpha,\beta))\bigr)/c,\qquad(26)$$
--   $$\mathbf m(N^C_{\alpha,\beta}(d^{\mathrm{set}}))\ge\bigl(2^{-\alpha-K(\alpha)}+\tau(\max(\alpha,\beta))\bigr)/c,\qquad(27)$$
--   and both measures are at most
--   $$c\bigl(2^{-\alpha+c\log(\alpha+2)}+\tau(\max(\alpha,\beta))\bigr).\qquad(28)$$
--
--   With finite sets as models, nonstochastic objects are frequent in all eight cases.
--
--   Differences from the source:
--   - encoding: d_p is one fixed largest randomness p-test → every d_p with IsLargestPTest d_p, quantified before the constant c; reason: the source fixes an arbitrary largest test; constants are chosen after it
--   - encoding: K(α) as a real exponent → ∃ κ : ℕ, K(α) = κ, and the bound with κ; reason: K(α) is valued in ℕ ∪ {∞} in Lean; for an optimal decoder it is finite, and asserting the witness avoids any default value of a conversion at ∞
--   - encoding: ∑ 2^(−F(ω)) = ∞ (resp. < ∞) → the ℝ≥0∞ sum ∑' (1/2)^F(ω) = ⊤ (resp. ≠ ⊤); reason: series of nonnegative terms; no real-tsum default
-- source:
--   Vladimir Vovk, The universal measure of nonstochastic objects, STOC 2027 submission #11 (October 2026), SHA-256 1ca25c4b7c38d8f49718c9fecbc2a434a7592886b44992c4fbef31ab3f480078, Theorem 14, eqs. (26)–(28), p.13 (PDF p.13)

import Mathlib
import Definitions.Def_UniversalNonstochastic_Main_Effective
import Definitions.Def_UniversalNonstochastic_Main_UniversalMeasure
import Definitions.Def_UniversalNonstochastic_Main_Complexity
import Definitions.Def_UniversalNonstochastic_Main_ElementaryModels
import Definitions.Def_UniversalNonstochastic_Main_Supplement_Complexities
import Definitions.Def_UniversalNonstochastic_Main_Supplement_Deficiencies

open scoped ENNReal

namespace UniversalNonstochastic.Main.Supplement

/-- Theorem 14, p.13: let `F` and `d_p` be as in Theorem 13. There is `c > 0` such that for all
`α ∈ ℕ₀`, `β ∈ [0, ∞)` and each `d ∈ {d_e, d_p, d_K, d_F}` (writing `κ = K(α)`, a natural
number, and `T = τ(max(α, β))`):
(26) `m(N_{α,β}(d^set)) ≥ (2^{-α} + T)/c`,
(27) `m(N^C_{α,β}(d^set)) ≥ (2^{-α-κ} + T)/c`,
(28) both measures are at most `c (2^{-α + c log₂(α+2)} + T)`. -/
theorem theorem_14 (m : UniversalSemimeasure) (U : OptimalPrefixDecoder) (V : OptimalPlainDecoder)
    (F : ℕ+ → ℕ) (hF : IsUpperSemicomputableNat F)
    (hdiv : ∑' ω : ℕ+, (2⁻¹ : ℝ≥0∞) ^ F ω = ⊤)
    (dp : ℕ+ → ElemMeasure → ℕ∞) (hdp : IsLargestPTest dp) :
    ∃ c : ℝ, 0 < c ∧ ∀ (α : ℕ) (β : ℝ), 0 ≤ β →
      ∃ κ : ℕ, KNat U α = κ ∧
        ∀ d : ℕ+ → ElemMeasure → EReal,
          (d = de U ∨ d = pDeficiency dp ∨ d = dK U ∨ d = dF F) →
            -- (26)
            ((2 : ℝ) ^ (-(α : ℝ)) + tail m (max (α : ℝ) β)) / c ≤
                mass m (nonQuasiStochastic U (dset d) α β) ∧
            -- (27)
            ((2 : ℝ) ^ (-(α : ℝ) - κ) + tail m (max (α : ℝ) β)) / c ≤
                mass m (nonQuasiStochasticC V (dset d) α β) ∧
            -- (28) for `N_{α,β}(d^set)`
            mass m (nonQuasiStochastic U (dset d) α β) ≤
                c * ((2 : ℝ) ^ (-(α : ℝ) + c * Real.logb 2 ((α : ℝ) + 2)) +
                  tail m (max (α : ℝ) β)) ∧
            -- (28) for `N^C_{α,β}(d^set)`
            mass m (nonQuasiStochasticC V (dset d) α β) ≤
                c * ((2 : ℝ) ^ (-(α : ℝ) + c * Real.logb 2 ((α : ℝ) + 2)) +
                  tail m (max (α : ℝ) β)) := by sorry

end UniversalNonstochastic.Main.Supplement
