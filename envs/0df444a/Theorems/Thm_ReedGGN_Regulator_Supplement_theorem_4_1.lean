-- Prove2me | Theorems.Thm_ReedGGN_Regulator_Supplement_theorem_4_1
-- name    : ReedGGN.Regulator.Supplement.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:10:18.603838+00:00
-- url     : https://prove2.me/theorems/f4377058-8795-412e-ad5c-0663da8ad7be
-- title:
--   Theorem 4.1 (corrected: time-zero arrivals)
-- statement:
--   Let the stochastic FCFS queues have service CDF $F$, tail $G=1-F$, and arbitrary initial-residual CDF $F_0$ with tail $\bar F_0$. Suppose the initial fluid counts and fluid arrivals converge jointly,
--
--   $$(\bar Q_0^N,\bar A^N)\Rightarrow(\bar Q_0,\bar A),$$
--
--   where $\bar A$ is almost surely continuous. The limits may be random and dependent. Then $\bar Q^N\Rightarrow\bar Q$ in J₁, where $\bar Q$ is the unique strong solution, at all $t\ge0$, of
--
--   $$\bar Q(t)=\min(\bar Q_0,1)\bar F_0(t)+(\bar Q_0-1)^+G(t)+\int_{[0,t]}G(t-s)d\bar A(s)+\int_{[0,t]}(\bar Q(t-s)-1)^+dF(s).$$
--
--   The solution is a measurable nonanticipating functional of the specified initial count and arrival path, unique among càdlàg paths on nonnegative times. The limit may jump for atomic service or residual distributions. This supplies the full fluid process approximation used later in the diffusion analysis.
--
--   Differences from the source:
--   - encoding: weak convergence in the maximum product J₁ metric on nonnegative-time càdlàg paths → full path-law coupling with scalar J₁ time changes separately for each path coordinate; N=n+1; reason: Skorohod representation on the Polish path space gives the same weak convergence, including discontinuous limits; indexing never divides by zero
--   - reading: FCFS queues with iid service primitives; the centering in (2.3) conditions on arrival and waiting times → earliest-available-server recursion and fresh services independent of the initial data and arrivals; initial count and arrivals may depend on one another; reason: the recursion uses only earlier services and encodes the queue and its nonanticipation, not a noise limit; pp.6–7 and 10
--   - encoding: arbitrary locally finite arrival counting processes, including finitely many total arrivals → published sample paths are extended after each finite horizon and observed only before that horizon; reason: the immutable SamplePath has real arrival times at every index; horizon extensions avoid excluding finite arrival streams and do not change any observed count or service start
--   - correction: the displayed convolution integrals do not specify a separate initial-mass term; (A.69) subtracts the initial value → queue arrival convolutions include the burst at zero, with G(t)x(0) added to the increment convolution; reason: pp.6–7 explicitly allow A(0)>0 and Q₀=Q(0−); for a burst c at zero its surviving contribution is cG(t), whereas an increment-only integral would give zero; see DISPROOF.md
--   - reading: unique strong solution and the regulator functional φ → a measurable nonanticipating functional satisfying the whole equation and unique among all càdlàg solutions on nonnegative times; reason: StrongFor makes the pathwise meaning explicit; equality on nonnegative-time paths is EqOn [0,∞) for their real-time extensions
--   - generalization: a unique strong solution for the stochastic initial data and driving processes in the theorem → a single measurable nonanticipating solution functional on every real initial coordinate and every càdlàg path-coordinate tuple; reason: the published regulator theorem applies to every càdlàg input; each displayed driver is càdlàg on this larger deterministic domain, and specializing to the source stochastic inputs gives its entire claim
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, Theorem 4.1, p.12

import Mathlib
import Definitions.Def_ReedGGN_Regulator_Supplement_Drivers

open MeasureTheory ProbabilityTheory Filter Topology

open scoped NNReal ENNReal

namespace ReedGGN.Regulator.Supplement

theorem theorem_4_1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ μ₀ : Measure ℝ) (q : QueueFamily Ω P μ μ₀)
    (Q₀ : Ω → ℝ) (A : Ω → RPath)
    (hA : ∀ᵐ ω ∂P, Continuous (A ω))
    (hinput : WeakJ1 P P (fun n ω => initialArrival (q0bar q n ω) (abar q n ω))
      (fun ω => initialArrival (Q₀ ω) (A ω))) :
    ∃ Φ : State 1 → RPath,
      StrongFor μ (-1) (fluidDriver μ μ₀) Φ ∧
      WeakJ1 P P (fun n ω => one (qbar q n ω))
        (fun ω => one (Φ (initialArrival (Q₀ ω) (A ω)))) := by sorry

end ReedGGN.Regulator.Supplement
