-- Prove2me | Theorems.Thm_ReedGGN_Regulator_Supplement_proposition_5_2
-- name    : ReedGGN.Regulator.Supplement.proposition_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:12:12.881376+00:00
-- url     : https://prove2.me/theorems/841fb3c1-01fc-4d44-b899-d99220be3b79
-- title:
--   Proposition 5.2
-- statement:
--   Assume the §5 arrival FCLT and staffing conditions, equilibrium initial residuals, and the primitive independence invoked on p.22. If $\tilde Q_0^N\Rightarrow\tilde Q_0$, there exists a joint realization of the limiting primitives with the specified initial-count and arrival marginal laws such that
--
--   $$(\tilde Q_0^N,\tilde W_0^N,\tilde A^N,\tilde M_2^N)\Rightarrow(\tilde Q_0,\tilde W_0(F_e),\tilde\xi,\tilde M_2)$$
--
--   in $\mathbb R\times D^3$ with its maximum product J₁ topology. The initial count, standard Brownian bridge, arrival limit and centered Gaussian service noise are mutually independent; the service noise has exactly Proposition 5.1's covariance. The arrival limit is continuous but need not be Gaussian. This joint result supplies all the primitive drivers and their dependence structure, rather than only their marginal limits.
--
--   Differences from the source:
--   - encoding: weak convergence in the maximum product J₁ metric on nonnegative-time càdlàg paths → full path-law coupling with scalar J₁ time changes separately for each path coordinate; N=n+1; reason: Skorohod representation on the Polish path space gives the same weak convergence, including discontinuous limits; indexing never divides by zero
--   - reading: FCFS queues with iid service primitives; the centering in (2.3) conditions on arrival and waiting times → earliest-available-server recursion and fresh services independent of the initial data and arrivals; initial count and arrivals may depend on one another; reason: the recursion uses only earlier services and encodes the queue and its nonanticipation, not a noise limit; pp.6–7 and 10
--   - encoding: arbitrary locally finite arrival counting processes, including finitely many total arrivals → published sample paths are extended after each finite horizon and observed only before that horizon; reason: the immutable SamplePath has real arrival times at every index; horizon extensions avoid excluding finite arrival streams and do not change any observed count or service start
--   - reading: the joint convergence proof on p.22 invokes independence of the four full prelimit primitive blocks → PrimitiveIndependent is a §5 hypothesis, and LimitLaws asserts mutual independence of count, full bridge, arrival limit and service noise in the conclusion; reason: this is the independence explicitly used in Proposition 5.2; it is not imposed on Theorem 4.1, nor on the two initial-count terms of the diffusion input
--   - encoding: limits specified by their marginal laws and mutual independence → existence on a probability space of a joint realization with the given count and arrival marginals, standard bridge and exact Gaussian service law; reason: the source does not fix a coupling of arbitrary marginal limit variables; the independent realization pins down the full limit law rather than assuming a chosen joint law
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, Proposition 5.2, p.21

import Mathlib
import Definitions.Def_ReedGGN_Regulator_Supplement_Drivers

open MeasureTheory ProbabilityTheory Filter Topology

open scoped NNReal ENNReal

namespace ReedGGN.Regulator.Supplement

theorem proposition_5_2
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ μ₀ : Measure ℝ) (q : QueueFamily Ω P μ μ₀)
    (ρ : ℕ → ℝ) (β : ℝ) (ξ : Ω → RPath) (Q₀ : Ω → ℝ)
    (hHT : HeavyTraffic q ρ β ξ) (heq : EquilibriumResidual μ μ₀)
    (hind : PrimitiveIndependent q)
    (hinit : WeakJ1 P P (fun n ω => scalar (q0diff q n ω)) (fun ω => scalar (Q₀ ω))) :
    ∃ (S : Type) (_ : MeasurableSpace S) (R : Measure S) (L : LimitData S),
      IsProbabilityMeasure R ∧ LimitLaws R μ L P Q₀ ξ ∧
      WeakJ1 P R (fun n ω => three (q0diff q n ω) (wdiff q n ω)
        (adiff q ρ n ω) (mdiff q n ω)) (primitiveLimit μ L) := by sorry

end ReedGGN.Regulator.Supplement
