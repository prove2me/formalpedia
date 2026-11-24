-- Prove2me | Theorems.Thm_ReedGGN_Regulator_Supplement_corollary_5_1
-- name    : ReedGGN.Regulator.Supplement.corollary_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:10:38.817887+00:00
-- url     : https://prove2.me/theorems/d77a4974-12ab-4ba1-ac6d-c5718f2510cc
-- title:
--   Corollary 5.1
-- statement:
--   Assume the §5 arrival FCLT and Halfin–Whitt conditions, with equilibrium residual CDF $F_0=F_e$, where $F_e(t)=\int_0^tG(u)du$. If the initial fluid counts satisfy $\bar Q_0^N\Rightarrow1$, then
--
--   $$\bar Q^N\Rightarrow1\quad\text{in }D[0,\infty)\text{ with J₁}. $$
--
--   Here the right side is the constant path one. This is convergence of the actual queues, beyond the already published inspection calculation that the constant path solves the limiting equation.
--
--   Differences from the source:
--   - encoding: weak convergence in the maximum product J₁ metric on nonnegative-time càdlàg paths → full path-law coupling with scalar J₁ time changes separately for each path coordinate; N=n+1; reason: Skorohod representation on the Polish path space gives the same weak convergence, including discontinuous limits; indexing never divides by zero
--   - reading: FCFS queues with iid service primitives; the centering in (2.3) conditions on arrival and waiting times → earliest-available-server recursion and fresh services independent of the initial data and arrivals; initial count and arrivals may depend on one another; reason: the recursion uses only earlier services and encodes the queue and its nonanticipation, not a noise limit; pp.6–7 and 10
--   - encoding: arbitrary locally finite arrival counting processes, including finitely many total arrivals → published sample paths are extended after each finite horizon and observed only before that horizon; reason: the immutable SamplePath has real arrival times at every index; horizon extensions avoid excluding finite arrival streams and do not change any observed count or service start
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, Corollary 5.1, p.18

import Mathlib
import Definitions.Def_ReedGGN_Regulator_Supplement_Drivers

open MeasureTheory ProbabilityTheory Filter Topology

open scoped NNReal ENNReal

namespace ReedGGN.Regulator.Supplement

theorem corollary_5_1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ μ₀ : Measure ℝ) (q : QueueFamily Ω P μ μ₀)
    (ρ : ℕ → ℝ) (β : ℝ) (ξ : Ω → RPath)
    (hHT : HeavyTraffic q ρ β ξ) (heq : EquilibriumResidual μ μ₀)
    (hinit : WeakJ1 P P (fun n ω => scalar (q0bar q n ω)) (fun _ => scalar 1)) :
    WeakJ1 P P (fun n ω => one (qbar q n ω)) (fun _ => one (fun _ => 1)) := by sorry

end ReedGGN.Regulator.Supplement
