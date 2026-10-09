-- Prove2me | Theorems.Thm_StatComplexityDM_TabularPS_global_simulation_lemma
-- name    : StatComplexityDM.TabularPS.global_simulation_lemma
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:25:55.803651+00:00
-- url     : https://prove2.me/theorems/57e4975f-d066-4d11-acc3-2df0106418f5
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
--   **Formalization Note** Rewards and all trajectory alphabets are finite; $D_H$ is represented as the square root of the published squared Hellinger distance. The final transition to the terminal state is omitted from the law. Only the appendix's almost-sure total-reward bound is assumed; individual rewards need not lie in $[0,1]$.
-- source:
--   arXiv:2112.13487v3, Lemma F.2, (142)–(143), p. 107

import Mathlib
import Definitions.Def_StatComplexityDM_TabularPS_MDP
import Definitions.Def_StatComplexityDM_TabularPS_EpisodeTotalInUnitInterval

namespace StatComplexityDM.TabularPS

/-- Lemma F.2, (142)–(143), p. 107. -/
theorem global_simulation_lemma {S A W : Type*}
    [Fintype S] [Fintype A] [Fintype W] [Nonempty S] [Nonempty A] [Nonempty W]
    (H : ℕ) (hH : 1 ≤ H) (d1 : S → ℝ) (rv : W → ℝ)
    (M M' : TabMDP S A W H) (π : Policy S A H) (η : ℝ)
    (hd1 : StatComplexityDM.LowerBound.IsDist d1) (hM : IsTabMDP M ∧ EpisodeTotalInUnitInterval d1 rv M)
    (hM' : IsTabMDP M' ∧ EpisodeTotalInUnitInterval d1 rv M')
    (hπ : IsPolicy π) (hη : 0 < η) :
    |value d1 rv M π - value d1 rv M' π| ≤
        FoundationsRL.GeneralDM.totalVariationDiscrete (trajLaw d1 M π) (trajLaw d1 M' π) ∧
    FoundationsRL.GeneralDM.totalVariationDiscrete (trajLaw d1 M π) (trajLaw d1 M' π) ≤
        Real.sqrt (FoundationsRL.GeneralDM.hellingerSq (trajLaw d1 M π) (trajLaw d1 M' π)) ∧
    Real.sqrt (FoundationsRL.GeneralDM.hellingerSq (trajLaw d1 M π) (trajLaw d1 M' π)) ≤
        1 / (2 * η) + η / 2 *
          FoundationsRL.GeneralDM.hellingerSq (trajLaw d1 M π) (trajLaw d1 M' π) := by sorry

end StatComplexityDM.TabularPS
