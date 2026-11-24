-- Prove2me | Theorems.Thm_ReedGGN_Regulator_Supplement_theorem_5_1
-- name    : ReedGGN.Regulator.Supplement.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:14:28.645482+00:00
-- url     : https://prove2.me/theorems/722df210-0565-4312-bca8-0739ac14f8fb
-- title:
--   Theorem 5.1 (corrected: time-zero arrivals and noise labels)
-- statement:
--   Let the stochastic FCFS queues satisfy the §5 arrival FCLT and staffing conditions with arbitrary $\beta\in\mathbb R$, fixed nonnegative mean-one service law $F$, equilibrium initial residuals, and the primitive independence used in Proposition 5.2. If $\tilde Q_0^N\Rightarrow\tilde Q_0$, choose a joint realization of mutually independent $\tilde Q_0,\tilde W_0,\tilde\xi,\tilde M_2$, with the given count and arrival laws, standard Brownian bridge and the exact Gaussian service covariance. Put $\bar F_e=1-F_e$, $\tilde H=\tilde Q_0\bar F_e$ and
--
--   $$\tilde M_Q=\tilde Q_0^+(G-\bar F_e),\qquad\tilde Q_I=\tilde H+\tilde W_0(F_e)+K_G^{\rm cl}\tilde\xi+\tilde M_2.$$
--
--   Then the actual centered queues converge in J₁:
--
--   $$\tilde Q^N\Rightarrow\varphi_F^0(\tilde M_Q+\tilde Q_I-\beta F_e).$$
--
--   The regulator output is specified as the measurable nonanticipating unique càdlàg solution of the complete stochastic convolution equation. All four terms of $\tilde Q_I$ and the initial-excess correction remain present. The arrival limit is an arbitrary continuous FCLT limit, and the entire input need not be Gaussian. This is the general-service Halfin–Whitt process limit, with no additional service moment condition.
--
--   Differences from the source:
--   - encoding: weak convergence in the maximum product J₁ metric on nonnegative-time càdlàg paths → full path-law coupling with scalar J₁ time changes separately for each path coordinate; N=n+1; reason: Skorohod representation on the Polish path space gives the same weak convergence, including discontinuous limits; indexing never divides by zero
--   - reading: FCFS queues with iid service primitives; the centering in (2.3) conditions on arrival and waiting times → earliest-available-server recursion and fresh services independent of the initial data and arrivals; initial count and arrivals may depend on one another; reason: the recursion uses only earlier services and encodes the queue and its nonanticipation, not a noise limit; pp.6–7 and 10
--   - encoding: arbitrary locally finite arrival counting processes, including finitely many total arrivals → published sample paths are extended after each finite horizon and observed only before that horizon; reason: the immutable SamplePath has real arrival times at every index; horizon extensions avoid excluding finite arrival streams and do not change any observed count or service start
--   - reading: the joint convergence proof on p.22 invokes independence of the four full prelimit primitive blocks → PrimitiveIndependent is a §5 hypothesis, and LimitLaws asserts mutual independence of count, full bridge, arrival limit and service noise in the conclusion; reason: this is the independence explicitly used in Proposition 5.2; it is not imposed on Theorem 4.1, nor on the two initial-count terms of the diffusion input
--   - encoding: limits specified by their marginal laws and mutual independence → existence on a probability space of a joint realization with the given count and arrival marginals, standard bridge and exact Gaussian service law; reason: the source does not fix a coupling of arbitrary marginal limit variables; the independent realization pins down the full limit law rather than assuming a chosen joint law
--   - correction: the displayed convolution integrals do not specify a separate initial-mass term; (A.69) subtracts the initial value → queue arrival convolutions include the burst at zero, with G(t)x(0) added to the increment convolution; reason: pp.6–7 explicitly allow A(0)>0 and Q₀=Q(0−); for a burst c at zero its surviving contribution is cG(t), whereas an increment-only integral would give zero; see DISPROOF.md
--   - reading: unique strong solution and the regulator functional φ → a measurable nonanticipating functional satisfying the whole equation and unique among all càdlàg solutions on nonnegative times; reason: StrongFor makes the pathwise meaning explicit; equality on nonnegative-time paths is EqOn [0,∞) for their real-time extensions
--   - correction: (5.9) swaps the scaled arrival and service noise labels → M₁ is the arrival convolution and M₂ is fresh-service noise; reason: (5.7), (5.20) and (A.58) identify the intended labels and leave the full four-term input intact
--   - generalization: a unique strong solution for the stochastic initial data and driving processes in the theorem → a single measurable nonanticipating solution functional on every real initial coordinate and every càdlàg path-coordinate tuple; reason: the published regulator theorem applies to every càdlàg input; each displayed driver is càdlàg on this larger deterministic domain, and specializing to the source stochastic inputs gives its entire claim
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, Theorem 5.1, p.23

import Mathlib
import Definitions.Def_ReedGGN_Regulator_Supplement_Drivers

open MeasureTheory ProbabilityTheory Filter Topology

open scoped NNReal ENNReal

namespace ReedGGN.Regulator.Supplement

theorem theorem_5_1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ μ₀ : Measure ℝ) (q : QueueFamily Ω P μ μ₀)
    (ρ : ℕ → ℝ) (β : ℝ) (ξ : Ω → RPath) (Q₀ : Ω → ℝ)
    (hHT : HeavyTraffic q ρ β ξ) (heq : EquilibriumResidual μ μ₀)
    (hind : PrimitiveIndependent q)
    (hinit : WeakJ1 P P (fun n ω => scalar (q0diff q n ω)) (fun ω => scalar (Q₀ ω))) :
    ∃ (S : Type) (_ : MeasurableSpace S) (R : Measure S) (L : LimitData S)
        (Φ : State 3 → RPath),
      IsProbabilityMeasure R ∧ LimitLaws R μ L P Q₀ ξ ∧
      StrongFor μ 0 (diffusionDriver μ β) Φ ∧
      WeakJ1 P R (fun n ω => one (qdiff q n ω))
        (fun ω => one (Φ (primitiveLimit μ L ω))) := by sorry

end ReedGGN.Regulator.Supplement
