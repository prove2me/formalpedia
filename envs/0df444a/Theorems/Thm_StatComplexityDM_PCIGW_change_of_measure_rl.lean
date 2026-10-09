-- Prove2me | Theorems.Thm_StatComplexityDM_PCIGW_change_of_measure_rl
-- name    : StatComplexityDM.PCIGW.change_of_measure_rl
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:13:25.275438+00:00
-- url     : https://prove2.me/theorems/2ddcd757-fa64-4930-a305-d2580acd9b36
-- title:
--   Lemma 5.2 (53)–(55) — change of measure for reinforcement learning
-- statement:
--   Let $\mu$ be a finitely supported prior on normalized tabular MDPs and let $p$ be a finitely supported distribution on randomized nonstationary policies. Fix a normalized reference MDP $\bar M$ with the same initial distribution and an optimal policy $\pi_M$ for every model in the prior's support. Suppose $C_1,C_2>0$ and
--   $$
--   \mathbb E_{M\sim\mu,\pi\sim p}[f^M(\pi_M)-f^{\bar M}(\pi)]
--   \le C_1+C_2\,\mathbb E_{M\sim\mu,\pi\sim p}\mathbb E^{\bar M,\pi}
--      \left[\sum_{h=1}^{H}D_H^2(P_h^M,P_h^{\bar M})+D_H^2(R_h^M,R_h^{\bar M})\right].
--   $$
--   Then for every $\eta>0$,
--   $$
--   \mathbb E_{M\sim\mu,\pi\sim p}[f^M(\pi_M)-f^M(\pi)]
--   \le C_1+\frac1{4\eta}+(40HC_2+\eta)
--     \mathbb E_{M\sim\mu,\pi\sim p}[D_H^2(M(\pi),\bar M(\pi))].
--   $$
--   This is the bridge from local kernel error to the trajectory divergence in the decision-estimation coefficient.
--
--   **Formalization Note** Priors and policy distributions have finite support. The transition term at the terminal layer is zero. Every model satisfies the paper's almost-sure total-reward bound $\sum_h r_h\in[0,1]$. The maximizing property of $\pi_M$ is kept as part of the setting, although (55) is stated for the given $\pi_M$.
-- source:
--   arXiv:2112.13487v3, Lemma 5.2, (53)–(55), p. 33; proof p. 108

import Mathlib
import Definitions.Def_StatComplexityDM_PCIGW_MDP

namespace StatComplexityDM.PCIGW

/-- Lemma 5.2, (53)–(55), p. 33; finite-support priors and policy laws. -/
theorem change_of_measure_rl {S A W I J : Type*}
    [Fintype S] [Fintype A] [Fintype W] [Fintype I] [Fintype J]
    [Nonempty S] [Nonempty A] [Nonempty W]
    (H : ℕ) (hH : 1 ≤ H) (d1 : S → ℝ) (rv : W → ℝ)
    (Ms : I → StatComplexityDM.TabularPS.TabMDP S A W H) (w : I → ℝ)
    (Mbar : StatComplexityDM.TabularPS.TabMDP S A W H) (pol : J → StatComplexityDM.TabularPS.Policy S A H) (q : J → ℝ)
    (piStar : StatComplexityDM.TabularPS.TabMDP S A W H → StatComplexityDM.TabularPS.Policy S A H)
    (C1 C2 η : ℝ)
    (hd1 : StatComplexityDM.LowerBound.IsDist d1) (hw : StatComplexityDM.LowerBound.IsDist w) (hq : StatComplexityDM.LowerBound.IsDist q)
    (hMs : ∀ i, StatComplexityDM.TabularPS.IsTabMDP (Ms i) ∧ EpisodeRewardsNormalized d1 rv (Ms i))
    (hMbar : StatComplexityDM.TabularPS.IsTabMDP Mbar ∧ EpisodeRewardsNormalized d1 rv Mbar)
    (hpol : ∀ j, StatComplexityDM.TabularPS.IsPolicy (pol j))
    (hpiStar : ∀ i, StatComplexityDM.TabularPS.IsPolicy (piStar (Ms i)) ∧
      ∀ π, StatComplexityDM.TabularPS.IsPolicy π → StatComplexityDM.TabularPS.value d1 rv (Ms i) π ≤ StatComplexityDM.TabularPS.value d1 rv (Ms i) (piStar (Ms i)))
    (hC1 : 0 < C1) (hC2 : 0 < C2) (hη : 0 < η)
    (hbase : ∑ i, w i * ∑ j, q j *
      (StatComplexityDM.TabularPS.value d1 rv (Ms i) (piStar (Ms i)) - StatComplexityDM.TabularPS.value d1 rv Mbar (pol j)) ≤
        C1 + C2 * ∑ i, w i * ∑ j, q j *
          StatComplexityDM.TabularPS.expectedLocalHellinger d1 (Ms i) Mbar (pol j)) :
    ∑ i, w i * ∑ j, q j *
      (StatComplexityDM.TabularPS.value d1 rv (Ms i) (piStar (Ms i)) - StatComplexityDM.TabularPS.value d1 rv (Ms i) (pol j)) ≤
      C1 + 1 / (4 * η) + (40 * (H : ℝ) * C2 + η) *
        ∑ i, w i * ∑ j, q j *
          FoundationsRL.GeneralDM.hellingerSq
            (StatComplexityDM.TabularPS.trajLaw d1 (Ms i) (pol j)) (StatComplexityDM.TabularPS.trajLaw d1 Mbar (pol j)) := by sorry

end StatComplexityDM.PCIGW
