-- Prove2me | Theorems.Thm_UniversalNonstochastic_Main_Supplement_theorem_13
-- name    : UniversalNonstochastic.Main.Supplement.theorem_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:34:11.160179+00:00
-- url     : https://prove2.me/theorems/a27e1943-a438-4daf-9925-96e5c8dbd586
-- title:
--   Theorem 13 — omnibus bounds (18)–(25) for non-quasi-stochastic objects
-- statement:
--   Let $F:\mathcal X\to\mathbb N_0$ be upper semicomputable with $\sum_\omega2^{-F(\omega)}=\infty$, let $d_p$ be a largest randomness p-test, and write $N_{\alpha,\beta}(d)$ (models with $K(Q)\le\alpha$) and $N^C_{\alpha,\beta}(d)$ (models with $C(Q)\le\alpha$). There is $c>0$ such that for all $\alpha\in\mathbb N_0$ and $\beta\in[0,\infty)$:
--   $$2^{-\alpha}/c\le\mathbf m(N_{\alpha,\beta}(d_e))\le c\bigl(2^{-\alpha+K(\alpha)}+2^{-2^{\beta/2-c}}\bigr),\qquad(18)$$
--   $$2^{-\alpha}/c\le\mathbf m(N_{\alpha,\beta}(d_p))\le c\bigl(2^{-\alpha+K(\alpha)}+2^{-2^{\beta/2-c}}\bigr),\qquad(19)$$
--   $$2^{-\alpha}/c\le\mathbf m(N_{\alpha,\beta}(d_K))\le c\,2^{-\alpha+K(\alpha)},\qquad(20)$$
--   $$\bigl(2^{-\alpha}+\tau(\max(\alpha,\beta))\bigr)/c\le\mathbf m(N_{\alpha,\beta}(d_F))\le c\bigl(2^{-\alpha+K(\alpha)}+\tau(\max(\alpha,\beta))\bigr),\qquad(21)$$
--   $$2^{-\alpha-K(\alpha)}/c\le\mathbf m(N^C_{\alpha,\beta}(d_e))\le c\bigl(2^{-\alpha}+2^{-2^{\beta/2-c}}\bigr),\qquad(22)$$
--   $$2^{-\alpha-K(\alpha)}/c\le\mathbf m(N^C_{\alpha,\beta}(d_p))\le c\bigl(2^{-\alpha}+2^{-2^{\beta/2-c}}\bigr),\qquad(23)$$
--   $$2^{-\alpha-K(\alpha)}/c\le\mathbf m(N^C_{\alpha,\beta}(d_K))\le c\,2^{-\alpha},\qquad(24)$$
--   $$\bigl(2^{-\alpha-K(\alpha)}+\tau(\max(\alpha,\beta))\bigr)/c\le\mathbf m(N^C_{\alpha,\beta}(d_F))\le c\bigl(2^{-\alpha}+\tau(\max(\alpha,\beta))\bigr).\qquad(25)$$
--
--   Here $d_e(\omega\mid Q)=-\log Q(\{\omega\})-K(\omega\mid Q)$, $d_K$ and $d_F$ are as in (12), and the same constant $c$ appears in the factors, the divisors and the double exponents. For $d_e,d_p,d_K$ non-quasi-stochastic objects are rare; for $d_F$ they are frequent.
--
--   Differences from the source:
--   - encoding: d_p is one fixed largest randomness p-test → every d_p with IsLargestPTest d_p, quantified before the constant c; reason: the source fixes an arbitrary largest test; constants are chosen after it
--   - encoding: K(α) as a real exponent → ∃ κ : ℕ, K(α) = κ, and the bound with κ; reason: K(α) is valued in ℕ ∪ {∞} in Lean; for an optimal decoder it is finite, and asserting the witness avoids any default value of a conversion at ∞
--   - encoding: ∑ 2^(−F(ω)) = ∞ (resp. < ∞) → the ℝ≥0∞ sum ∑' (1/2)^F(ω) = ⊤ (resp. ≠ ⊤); reason: series of nonnegative terms; no real-tsum default
-- source:
--   Vladimir Vovk, The universal measure of nonstochastic objects, STOC 2027 submission #11 (October 2026), SHA-256 1ca25c4b7c38d8f49718c9fecbc2a434a7592886b44992c4fbef31ab3f480078, Theorem 13, eqs. (18)–(25), p.13 (PDF p.13); d_p defined on p.12

import Mathlib
import Definitions.Def_UniversalNonstochastic_Main_Effective
import Definitions.Def_UniversalNonstochastic_Main_UniversalMeasure
import Definitions.Def_UniversalNonstochastic_Main_Complexity
import Definitions.Def_UniversalNonstochastic_Main_ElementaryModels
import Definitions.Def_UniversalNonstochastic_Main_Supplement_Complexities
import Definitions.Def_UniversalNonstochastic_Main_Supplement_Deficiencies

open scoped ENNReal

namespace UniversalNonstochastic.Main.Supplement

/-- Theorem 13, p.13: let `F : 𝓧 → ℕ₀` be upper semicomputable with `∑_ω 2^{-F(ω)} = ∞`, and
let `d_p` be a largest randomness p-test. There is `c > 0` such that for all `α ∈ ℕ₀` and
`β ∈ [0, ∞)` (writing `κ = K(α)`, a natural number, and `T = τ(max(α, β))`), the sixteen
bounds (18)–(25) hold:
(18)–(21) for `N_{α,β}(d)` with `d = d_e, d_p, d_K, d_F`, and (22)–(25) for `N^C_{α,β}(d)`. -/
theorem theorem_13 (m : UniversalSemimeasure) (U : OptimalPrefixDecoder) (V : OptimalPlainDecoder)
    (F : ℕ+ → ℕ) (hF : IsUpperSemicomputableNat F)
    (hdiv : ∑' ω : ℕ+, (2⁻¹ : ℝ≥0∞) ^ F ω = ⊤)
    (dp : ℕ+ → ElemMeasure → ℕ∞) (hdp : IsLargestPTest dp) :
    ∃ c : ℝ, 0 < c ∧ ∀ (α : ℕ) (β : ℝ), 0 ≤ β →
      ∃ κ : ℕ, KNat U α = κ ∧
        -- (18)
        ((2 : ℝ) ^ (-(α : ℝ)) / c ≤ mass m (nonQuasiStochastic U (de U) α β) ∧
          mass m (nonQuasiStochastic U (de U) α β) ≤
            c * ((2 : ℝ) ^ (-(α : ℝ) + κ) + (2 : ℝ) ^ (-(2 : ℝ) ^ (β / 2 - c)))) ∧
        -- (19)
        ((2 : ℝ) ^ (-(α : ℝ)) / c ≤ mass m (nonQuasiStochastic U (pDeficiency dp) α β) ∧
          mass m (nonQuasiStochastic U (pDeficiency dp) α β) ≤
            c * ((2 : ℝ) ^ (-(α : ℝ) + κ) + (2 : ℝ) ^ (-(2 : ℝ) ^ (β / 2 - c)))) ∧
        -- (20)
        ((2 : ℝ) ^ (-(α : ℝ)) / c ≤ mass m (nonQuasiStochastic U (dK U) α β) ∧
          mass m (nonQuasiStochastic U (dK U) α β) ≤ c * (2 : ℝ) ^ (-(α : ℝ) + κ)) ∧
        -- (21)
        (((2 : ℝ) ^ (-(α : ℝ)) + tail m (max (α : ℝ) β)) / c ≤
            mass m (nonQuasiStochastic U (dF F) α β) ∧
          mass m (nonQuasiStochastic U (dF F) α β) ≤
            c * ((2 : ℝ) ^ (-(α : ℝ) + κ) + tail m (max (α : ℝ) β))) ∧
        -- (22)
        ((2 : ℝ) ^ (-(α : ℝ) - κ) / c ≤ mass m (nonQuasiStochasticC V (de U) α β) ∧
          mass m (nonQuasiStochasticC V (de U) α β) ≤
            c * ((2 : ℝ) ^ (-(α : ℝ)) + (2 : ℝ) ^ (-(2 : ℝ) ^ (β / 2 - c)))) ∧
        -- (23)
        ((2 : ℝ) ^ (-(α : ℝ) - κ) / c ≤ mass m (nonQuasiStochasticC V (pDeficiency dp) α β) ∧
          mass m (nonQuasiStochasticC V (pDeficiency dp) α β) ≤
            c * ((2 : ℝ) ^ (-(α : ℝ)) + (2 : ℝ) ^ (-(2 : ℝ) ^ (β / 2 - c)))) ∧
        -- (24)
        ((2 : ℝ) ^ (-(α : ℝ) - κ) / c ≤ mass m (nonQuasiStochasticC V (dK U) α β) ∧
          mass m (nonQuasiStochasticC V (dK U) α β) ≤ c * (2 : ℝ) ^ (-(α : ℝ))) ∧
        -- (25)
        (((2 : ℝ) ^ (-(α : ℝ) - κ) + tail m (max (α : ℝ) β)) / c ≤
            mass m (nonQuasiStochasticC V (dF F) α β) ∧
          mass m (nonQuasiStochasticC V (dF F) α β) ≤
            c * ((2 : ℝ) ^ (-(α : ℝ)) + tail m (max (α : ℝ) β))) := by sorry

end UniversalNonstochastic.Main.Supplement
