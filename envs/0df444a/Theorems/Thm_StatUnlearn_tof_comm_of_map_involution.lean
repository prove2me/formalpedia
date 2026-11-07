-- Prove2me | Theorems.Thm_StatUnlearn_tof_comm_of_map_involution
-- name    : StatUnlearn.tof_comm_of_map_involution
-- status  : Proved
-- author  : @2017Advanced@
-- created : 2026-11-06T20:10:36.348877+00:00
-- url     : https://prove2.me/theorems/049dc852-2e6c-4cf0-af4b-b0951ef2f092
-- title:
--   Symmetry of the trade-off function under a measure-preserving involution
-- statement:
--   Let $P$ and $Q$ be probability distributions on a measurable space $W$, and let $\rho:W\to W$ be a measurable map exchanging them, $\rho_*P=Q$ and $\rho_*Q=P$. Then $T(P,Q)=T(Q,P)$. The map $\psi\mapsto\psi\circ\rho$ is a bijection of the randomized tests preserving both errors ($\int\psi\circ\rho\,dP=\int\psi\,dQ$ and $\int(1-\psi\circ\rho)\,dQ=\int(1-\psi)\,dP$), so the two infima range over the same set. No optimality of any test is used, which is why this part of Lemma A.1 does not need Neyman–Pearson.
-- source:
--   Pandey, Kulkarni, "Statistical Unlearning of Distributions: A Hypothesis Testing Approach", arXiv:2605.16645, Appendix A.2, Lemma A.1 (`lem: GTOF`), symmetry eq. (A.3)

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Definitions.Def_su_tof
open MeasureTheory ProbabilityTheory

namespace StatUnlearn

theorem tof_comm_of_map_involution {W : Type*} [MeasurableSpace W]
    (ρ : W → W) (hinv : Function.Involutive ρ) (hρ : Measurable ρ)
    (P Q : Measure W) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : Measure.map ρ P = Q) (hQ : Measure.map ρ Q = P) (t : ℝ) :
    tof P Q t = tof Q P t := by
  sorry

end StatUnlearn
