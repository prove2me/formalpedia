-- Prove2me | Theorems.Thm_UniversalNonstochastic_Main_Supplement_theorem_7
-- name    : UniversalNonstochastic.Main.Supplement.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:30:42.150732+00:00
-- url     : https://prove2.me/theorems/935c5c20-70b3-4d21-8cbb-be3a0b82bb40
-- title:
--   Theorem 7 — $2^{-\alpha}/c\le\mathbf m(N^q_{\alpha,\beta})\le c(2^{-\alpha+K(\alpha)}+2^{-2^{\beta/2-c}})$
-- statement:
--   An object $\omega$ is $(\alpha,\beta)$-quasi-stochastic if some elementary probability measure $Q$ has $K(Q)\le\alpha$, $Q(\{\omega\})>0$ and $K(\omega\mid Q)\ge-\log Q(\{\omega\})-\beta$; $N^q_{\alpha,\beta}$ is the set of objects that are not. There is $c>0$ such that for all $\alpha\in\mathbb N_0$ and $\beta\in[0,\infty)$,
--   $$2^{-\alpha}/c\le\mathbf m(N^q_{\alpha,\beta})\le c\Bigl(2^{-\alpha+K(\alpha)}+2^{-2^{\beta/2-c}}\Bigr).$$
--
--   With probability measures as models, non-quasi-stochastic objects are exponentially rare, in contrast with Theorem 1.
--
--   Differences from the source:
--   - encoding: N^q_{α,β} with the clause Q({ω}) > 0 → the published N_{α,β}(d_e), where d_e(ω | Q) = +∞ when Q({ω}) = 0; reason: the source states N^q_{α,β} = N_{α,β}(d_e) on p.10; d_e = +∞ at Q({ω}) = 0 encodes the clause
--   - encoding: K(α) as a real exponent → ∃ κ : ℕ, K(α) = κ, and the bound with κ; reason: K(α) is valued in ℕ ∪ {∞} in Lean; for an optimal decoder it is finite, and asserting the witness avoids any default value of a conversion at ∞
-- source:
--   Vladimir Vovk, The universal measure of nonstochastic objects, STOC 2027 submission #11 (October 2026), SHA-256 1ca25c4b7c38d8f49718c9fecbc2a434a7592886b44992c4fbef31ab3f480078, Theorem 7, p.8 (PDF p.8); definition of N^q on p.8

import Mathlib
import Definitions.Def_UniversalNonstochastic_Main_UniversalMeasure
import Definitions.Def_UniversalNonstochastic_Main_Complexity
import Definitions.Def_UniversalNonstochastic_Main_ElementaryModels
import Definitions.Def_UniversalNonstochastic_Main_Supplement_Complexities

namespace UniversalNonstochastic.Main.Supplement

/-- Theorem 7, p.8: there is `c > 0` such that for all `α ∈ ℕ₀` and `β ∈ [0, ∞)`,
`2^{-α}/c ≤ m(N^q_{α,β}) ≤ c (2^{-α+K(α)} + 2^{-2^{β/2-c}})`, where
`N^q_{α,β} = N_{α,β}(d_e)`. The conclusion also records that `K(α)` is a natural number `κ`. -/
theorem theorem_7 (m : UniversalSemimeasure) (U : OptimalPrefixDecoder) :
    ∃ c : ℝ, 0 < c ∧ ∀ (α : ℕ) (β : ℝ), 0 ≤ β →
      ∃ κ : ℕ, KNat U α = κ ∧
        (2 : ℝ) ^ (-(α : ℝ)) / c ≤ mass m (nonQuasiStochastic U (de U) α β) ∧
        mass m (nonQuasiStochastic U (de U) α β) ≤
          c * ((2 : ℝ) ^ (-(α : ℝ) + κ) + (2 : ℝ) ^ (-(2 : ℝ) ^ (β / 2 - c))) := by sorry

end UniversalNonstochastic.Main.Supplement
