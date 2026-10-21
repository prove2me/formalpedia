-- Prove2me | Theorems.Thm_SeqRankAgg_Optimality_lemma_11
-- name    : SeqRankAgg.Optimality.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:37:31.522868+00:00
-- url     : https://prove2.me/theorems/8655f38b-bf98-4c05-90f9-fea2c5e915d4
-- title:
--   Lemma 11, p. 25 — stopped likelihood-ratio tail
-- statement:
--   Fix a true parameter $\theta$, a different alternative $\tilde\theta\ne\theta$, an adaptive pair-selection policy, a stopping time $T$, a deterministic truncation time $\tau$, and $A>0$. Writing $l_n$ for the comparison log likelihood and $\mathbb P_\theta$ for the induced trajectory law,
--
--   $$
--   \mathbb P_\theta\!\left(l_{T\wedge\tau}(\tilde\theta)-l_{T\wedge\tau}(\theta)\ge A\right)\le e^{-A}.
--   $$
--
--   The bound controls a likelihood ratio even when comparison pairs are selected adaptively and the observation horizon is stopped.
--
--   **Formalization Note** The paper’s likelihood uses the selected pairs and binary outcomes, and the truncation makes the prefix length finite. The standing model assumptions and positivity of $f^a_\theta(x)$ are explicit.
-- source:
--   Chen, Chen & Li, Asymptotically optimal sequential design for rank aggregation, arXiv:1710.06056v1, p. 25, Lemma 11; p. 42, Appendix F

import Mathlib
import Definitions.Def_SeqRankAgg_Optimality_Model

open MeasureTheory Filter
open scoped ENNReal

namespace SeqRankAgg.Optimality

theorem lemma_11 {m : ℕ} (hm : 1 ≤ m) (M : CompModel m)
    (ρ : (Fin m → ℝ) → ℝ≥0∞)
    (hA1 : A1 ρ) (hA2 : A2 ρ) (hA3 : A3 M ρ)
    (hA4 : A4 M ρ) (hA5 : A5 ρ) (hA7 : A7 M ρ)
    (θ θ' : Fin m → ℝ) (hne : θ' ≠ θ)
    (A : BanditAlgorithm.BanditPolicy (numPairs m))
    (T : Trajectory m → ℕ∞) (hT : BanditAlgorithm.IsBanditStoppingTime T)
    (τ : ℕ) (threshold : ℝ) (hthreshold : 0 < threshold) :
    BanditAlgorithm.banditTrajMeasure (bandit M θ) A
      {ω | let n := (min (T ω) (τ : ℕ∞)).untopD τ
        threshold ≤ loglikTraj M n ω θ' - loglikTraj M n ω θ} ≤
      ENNReal.ofReal (Real.exp (-threshold)) := by sorry

end SeqRankAgg.Optimality
