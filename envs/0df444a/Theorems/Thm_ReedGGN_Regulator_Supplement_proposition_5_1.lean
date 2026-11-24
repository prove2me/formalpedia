-- Prove2me | Theorems.Thm_ReedGGN_Regulator_Supplement_proposition_5_1
-- name    : ReedGGN.Regulator.Supplement.proposition_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:11:16.452919+00:00
-- url     : https://prove2.me/theorems/92aae6c0-1a5e-44d5-9bc6-b2902ca6ccef
-- title:
--   Proposition 5.1 (corrected: right-continuous survival)
-- statement:
--   Under the §5 heavy-traffic setup, equilibrium initial residuals and $\bar Q_0^N\Rightarrow1$, let $\tilde M_2^N=M_2^N/\sqrt N$ use the actual service-entry times. Define its deterministic-entry comparison by
--
--   $$\hat M_2^N(t)=N^{-1/2}\sum_{1\le i\le Nt}\bigl(\mathbf1\{i/N+\eta_i>t\}-G(t-i/N)\bigr).$$
--
--   There is a continuous centered Gaussian process $\tilde M_2$ such that
--
--   $$(\tilde M_2^N,\hat M_2^N)\Rightarrow(\tilde M_2,\tilde M_2),\qquad E[\tilde M_2(t)\tilde M_2(t+\delta)]=\int_0^tG(t+\delta-u)F(t-u)du\quad(t,\delta\ge0).$$
--
--   The convergence is joint in the maximum product J₁ topology, to two copies of the same random process, not independent copies. This identifies the service noise law for the diffusion input. The right-continuous indicator corrects the printed boundary slip.
--
--   Differences from the source:
--   - encoding: weak convergence in the maximum product J₁ metric on nonnegative-time càdlàg paths → full path-law coupling with scalar J₁ time changes separately for each path coordinate; N=n+1; reason: Skorohod representation on the Polish path space gives the same weak convergence, including discontinuous limits; indexing never divides by zero
--   - reading: FCFS queues with iid service primitives; the centering in (2.3) conditions on arrival and waiting times → earliest-available-server recursion and fresh services independent of the initial data and arrivals; initial count and arrivals may depend on one another; reason: the recursion uses only earlier services and encodes the queue and its nonanticipation, not a noise limit; pp.6–7 and 10
--   - encoding: arbitrary locally finite arrival counting processes, including finitely many total arrivals → published sample paths are extended after each finite horizon and observed only before that horizon; reason: the immutable SamplePath has real arrival times at every index; horizon extensions avoid excluding finite arrival streams and do not change any observed count or service start
--   - encoding: limits specified by their marginal laws and mutual independence → existence on a probability space of a joint realization with the given count and arrival marginals, standard bridge and exact Gaussian service law; reason: the source does not fix a coupling of arbitrary marginal limit variables; the independent realization pins down the full limit law rather than assuming a chosen joint law
--   - correction: p.20 prints the survival indicator with ≥ → the indicator is >, as in (2.5); reason: for service time 1, at t=i/N+1 the printed summand has a value one larger than its right limit, so is not càdlàg; the correction selects the right-continuous process without restricting any service law
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, Proposition 5.1, p.20

import Mathlib
import Definitions.Def_ReedGGN_Regulator_Supplement_Drivers

open MeasureTheory ProbabilityTheory Filter Topology

open scoped NNReal ENNReal

namespace ReedGGN.Regulator.Supplement

theorem proposition_5_1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ μ₀ : Measure ℝ) (q : QueueFamily Ω P μ μ₀)
    (ρ : ℕ → ℝ) (β : ℝ) (ξ : Ω → RPath)
    (hHT : HeavyTraffic q ρ β ξ) (heq : EquilibriumResidual μ μ₀)
    (hinit : WeakJ1 P P (fun n ω => scalar (q0bar q n ω)) (fun _ => scalar 1)) :
    ∃ (S : Type) (_ : MeasurableSpace S) (R : Measure S) (M : S → RPath),
      IsProbabilityMeasure R ∧ ServiceGaussian R μ M ∧
      WeakJ1 P R (fun n ω => two (mdiff q n ω) (mhat q n ω))
        (fun ω => two (M ω) (M ω)) := by sorry

end ReedGGN.Regulator.Supplement
