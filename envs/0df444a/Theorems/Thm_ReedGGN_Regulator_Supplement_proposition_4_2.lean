-- Prove2me | Theorems.Thm_ReedGGN_Regulator_Supplement_proposition_4_2
-- name    : ReedGGN.Regulator.Supplement.proposition_4_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T05:08:33.370003+00:00
-- url     : https://prove2.me/theorems/4a73fbe8-58ae-4566-8eff-1366ee5b5568
-- title:
--   Proposition 4.2
-- statement:
--   Let $Q^N$ be the stochastic non-idling FCFS queues of §2 with fixed nonnegative service law $F$ of finite mean one. Write $M_2^N$ for the two centered fresh-service sums (2.5), computed from their actual service-entry times, and $\bar M_2^N=M_2^N/N$. Then
--
--   $$\bar M_2^N\Rightarrow0\quad\text{in }D[0,\infty)\text{ with J₁}. $$
--
--   This removes the actual-entry service noise at fluid scale. The noise limit is a conclusion, not an assumption in the stochastic model.
--
--   Differences from the source:
--   - encoding: weak convergence in the maximum product J₁ metric on nonnegative-time càdlàg paths → full path-law coupling with scalar J₁ time changes separately for each path coordinate; N=n+1; reason: Skorohod representation on the Polish path space gives the same weak convergence, including discontinuous limits; indexing never divides by zero
--   - reading: FCFS queues with iid service primitives; the centering in (2.3) conditions on arrival and waiting times → earliest-available-server recursion and fresh services independent of the initial data and arrivals; initial count and arrivals may depend on one another; reason: the recursion uses only earlier services and encodes the queue and its nonanticipation, not a noise limit; pp.6–7 and 10
--   - encoding: arbitrary locally finite arrival counting processes, including finitely many total arrivals → published sample paths are extended after each finite horizon and observed only before that horizon; reason: the immutable SamplePath has real arrival times at every index; horizon extensions avoid excluding finite arrival streams and do not change any observed count or service start
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, Proposition 4.2, p.12

import Mathlib
import Definitions.Def_ReedGGN_Regulator_Supplement_Drivers

open MeasureTheory ProbabilityTheory Filter Topology

open scoped NNReal ENNReal

namespace ReedGGN.Regulator.Supplement

theorem proposition_4_2
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ μ₀ : Measure ℝ) (q : QueueFamily Ω P μ μ₀) :
    WeakJ1 P P (fun n ω => one (mbar q n ω)) (fun _ => one (fun _ => 0)) := by sorry

end ReedGGN.Regulator.Supplement
