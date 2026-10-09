-- Prove2me | Theorems.Thm_StatComplexityDM_PCIGW_pcigw_exploration_bias
-- name    : StatComplexityDM.PCIGW.pcigw_exploration_bias
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:13:56.484818+00:00
-- url     : https://prove2.me/theorems/acf78827-28d6-4993-951a-e42c549d0973
-- title:
--   Display (59) — PC-IGW exploration bias at most 2HSA/η
-- statement:
--   Under Algorithm 4, let $g^{\bar M}(\pi)=f^{\bar M}(\pi_{\bar M})-f^{\bar M}(\pi)$ and let $p$ be the normalized inverse gap weights on the distinct policies $\Psi\cup\{\pi_{\bar M}\}$. The expected estimated-model gap satisfies
--   $$
--   \mathbb E_{\pi\sim p}[g^{\bar M}(\pi)]\le\frac{2HSA}{\eta}.
--   $$
--   This bounds the exploration cost contributed by the cover policies in Proposition 5.6.
--
--   **Formalization Note** The normalizer is positive, as supplied by Proposition 5.7. The result is stated for finite nonempty state, action, and reward alphabets and $H\ge1$.
-- source:
--   arXiv:2112.13487v3, (59), p. 37

import Mathlib
import Definitions.Def_StatComplexityDM_PCIGW_Algorithm

namespace StatComplexityDM.PCIGW

/-- Display (59), p. 37: the PC-IGW policy's exploration bias. -/
theorem pcigw_exploration_bias {S A W : Type*}
    [Fintype S] [Fintype A] [Fintype W]
    [Nonempty S] [Nonempty A] [Nonempty W]
    (H : ℕ) (hH : 1 ≤ H) (d1 : S → ℝ) (rv : W → ℝ)
    (Mbar : StatComplexityDM.TabularPS.TabMDP S A W H)
    (piStar : StatComplexityDM.TabularPS.TabMDP S A W H → StatComplexityDM.TabularPS.Policy S A H)
    (η lam : ℝ) (cover : Fin H → S → A → StatComplexityDM.TabularPS.Policy S A H)
    (hd1 : StatComplexityDM.LowerBound.IsDist d1)
    (hMbar : StatComplexityDM.TabularPS.IsTabMDP Mbar ∧ RewardsNormalized d1 rv Mbar)
    (hpiStar : IsOptimalSelector d1 rv piStar)
    (hη : 0 < η) (halg : IsPCIGW d1 rv Mbar piStar η cover lam) :
    ∑ π ∈ pcigwPsi Mbar piStar cover,
      pcigwWeight d1 rv Mbar piStar η lam π *
        gapBar d1 rv Mbar piStar π ≤
      2 * (H : ℝ) * Fintype.card S * Fintype.card A / η := by sorry

end StatComplexityDM.PCIGW
