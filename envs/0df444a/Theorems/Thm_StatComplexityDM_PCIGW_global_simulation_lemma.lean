-- Prove2me | Theorems.Thm_StatComplexityDM_PCIGW_global_simulation_lemma
-- name    : StatComplexityDM.PCIGW.global_simulation_lemma
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:12:34.001445+00:00
-- url     : https://prove2.me/theorems/d11b6163-c3b5-427c-af8e-7386acb91fe5
-- title:
--   Lemma F.2 (142)–(143) — global simulation bound for tabular MDPs
-- statement:
--   Consider two valid finite-horizon MDPs with the same initial distribution and a randomized nonstationary policy $\pi$. Suppose cumulative reward lies in $[0,1]$ almost surely in each model. If $M(\pi)$ and $M'(\pi)$ denote their full trajectory laws, then for every $\eta>0$,
--   $$
--   |f^M(\pi)-f^{M'}(\pi)|\le D_{TV}(M(\pi),M'(\pi))
--   \le D_H(M(\pi),M'(\pi))
--   \le\frac{1}{2\eta}+\frac{\eta}{2}D_H^2(M(\pi),M'(\pi)).
--   $$
--   The result turns a policy-value difference into a whole-trajectory divergence penalty.
--
--   **Formalization Note** Rewards and all trajectory alphabets are finite; $D_H$ is represented as the square root of the published squared Hellinger distance. The final transition to the terminal state is omitted from the law.
-- source:
--   arXiv:2112.13487v3, Lemma F.2, (142)–(143), p. 107

import Mathlib
import Definitions.Def_StatComplexityDM_PCIGW_MDP

namespace StatComplexityDM.PCIGW

/-- Lemma F.2, (142)–(143), p. 107. -/
theorem global_simulation_lemma {S A W : Type*}
    [Fintype S] [Fintype A] [Fintype W] [Nonempty S] [Nonempty A] [Nonempty W]
    (H : ℕ) (hH : 1 ≤ H) (d1 : S → ℝ) (rv : W → ℝ)
    (M M' : StatComplexityDM.TabularPS.TabMDP S A W H) (π : StatComplexityDM.TabularPS.Policy S A H) (η : ℝ)
    (hd1 : StatComplexityDM.LowerBound.IsDist d1) (hM : StatComplexityDM.TabularPS.IsTabMDP M ∧ EpisodeRewardsNormalized d1 rv M)
    (hM' : StatComplexityDM.TabularPS.IsTabMDP M' ∧ EpisodeRewardsNormalized d1 rv M')
    (hπ : StatComplexityDM.TabularPS.IsPolicy π) (hη : 0 < η) :
    |StatComplexityDM.TabularPS.value d1 rv M π - StatComplexityDM.TabularPS.value d1 rv M' π| ≤
        FoundationsRL.GeneralDM.totalVariationDiscrete (StatComplexityDM.TabularPS.trajLaw d1 M π) (StatComplexityDM.TabularPS.trajLaw d1 M' π) ∧
    FoundationsRL.GeneralDM.totalVariationDiscrete (StatComplexityDM.TabularPS.trajLaw d1 M π) (StatComplexityDM.TabularPS.trajLaw d1 M' π) ≤
        Real.sqrt (FoundationsRL.GeneralDM.hellingerSq (StatComplexityDM.TabularPS.trajLaw d1 M π) (StatComplexityDM.TabularPS.trajLaw d1 M' π)) ∧
    Real.sqrt (FoundationsRL.GeneralDM.hellingerSq (StatComplexityDM.TabularPS.trajLaw d1 M π) (StatComplexityDM.TabularPS.trajLaw d1 M' π)) ≤
        1 / (2 * η) + η / 2 *
          FoundationsRL.GeneralDM.hellingerSq (StatComplexityDM.TabularPS.trajLaw d1 M π) (StatComplexityDM.TabularPS.trajLaw d1 M' π) := by sorry

end StatComplexityDM.PCIGW
