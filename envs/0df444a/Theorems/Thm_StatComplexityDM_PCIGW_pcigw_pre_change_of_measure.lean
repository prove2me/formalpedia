-- Prove2me | Theorems.Thm_StatComplexityDM_PCIGW_pcigw_pre_change_of_measure
-- name    : StatComplexityDM.PCIGW.pcigw_pre_change_of_measure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:13:51.363571+00:00
-- url     : https://prove2.me/theorems/cdf8d872-994b-45ea-99ee-f08afe0713a2
-- title:
--   Proposition 5.6 proof, p. 38 — bound before change of measure
-- statement:
--   Let $p$ be Algorithm 4's normalized distribution for the estimated tabular MDP $\bar M$, with exploration rate $\eta>0$. For every normalized tabular MDP $M$, write $D_{TV}^2(P_h^M,P_h^{\bar M})+D_{TV}^2(R_h^M,R_h^{\bar M})$ for the two squared one-step discrepancies at a state-action pair. Then
--   $$
--   \mathbb E_{\pi\sim p}[f^M(\pi_M)-f^{\bar M}(\pi)]\le
--   \frac{4HSA}{\eta}+\frac{\eta H}{2}\,\mathbb E_{\pi\sim p}\mathbb E^{\bar M,\pi}\!\left[\sum_{h=1}^H(D_{TV}^2(P_h^M,P_h^{\bar M})+D_{TV}^2(R_h^M,R_h^{\bar M}))\right].
--   $$
--   The inequality is the bound immediately before Lemma 5.2 is applied in the proof of Proposition 5.6.
--
--   **Formalization Note** The last transition is to a deterministic terminal state, so its divergence contribution is zero. Per-stage rewards are nonnegative and normalized on every supported suffix, as required by the local simulation bound.
-- source:
--   arXiv:2112.13487v3, §5.2.2, proof of Proposition 5.6, p. 38, unnumbered display before Lemma 5.2

import Mathlib
import Definitions.Def_StatComplexityDM_PCIGW_Algorithm

namespace StatComplexityDM.PCIGW

/-- Proposition 5.6, proof p. 38: the displayed bound before applying
Lemma 5.2, with local total-variation discrepancies. -/
theorem pcigw_pre_change_of_measure {S A W : Type*}
    [Fintype S] [Fintype A] [Fintype W]
    [Nonempty S] [Nonempty A] [Nonempty W]
    (H : ℕ) (hH : 1 ≤ H) (d1 : S → ℝ) (rv : W → ℝ)
    (Mbar M : StatComplexityDM.TabularPS.TabMDP S A W H)
    (piStar : StatComplexityDM.TabularPS.TabMDP S A W H → StatComplexityDM.TabularPS.Policy S A H)
    (η lam : ℝ) (cover : Fin H → S → A → StatComplexityDM.TabularPS.Policy S A H)
    (hd1 : StatComplexityDM.LowerBound.IsDist d1)
    (hMbar : StatComplexityDM.TabularPS.IsTabMDP Mbar ∧ RewardsNormalized d1 rv Mbar)
    (hM : StatComplexityDM.TabularPS.IsTabMDP M ∧ RewardsNormalized d1 rv M)
    (hpiStar : IsOptimalSelector d1 rv piStar)
    (hη : 0 < η) (halg : IsPCIGW d1 rv Mbar piStar η cover lam) :
    ∑ π ∈ pcigwPsi Mbar piStar cover,
      pcigwWeight d1 rv Mbar piStar η lam π *
        (StatComplexityDM.TabularPS.value d1 rv M (piStar M) - StatComplexityDM.TabularPS.value d1 rv Mbar π) ≤
      4 * (H : ℝ) * Fintype.card S * Fintype.card A / η +
        η * (H : ℝ) / 2 *
          ∑ π ∈ pcigwPsi Mbar piStar cover,
            pcigwWeight d1 rv Mbar piStar η lam π *
              StatComplexityDM.TabularPS.expectedLocalTVSq d1 M Mbar π := by sorry

end StatComplexityDM.PCIGW
