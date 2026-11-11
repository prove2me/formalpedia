-- Prove2me | Theorems.Thm_SybilClinch_theorem_6_3
-- name    : SybilClinch.theorem_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:47:54.368737+00:00
-- url     : https://prove2.me/theorems/0988b99b-eb10-4f8f-b150-4ba717f0c15d
-- title:
--   Theorem 6.3 — two-sided termination, exact settlement and individual rationality
-- statement:
--   Let $\varphi$ be an admissible AMM and consider any profile of finite nonnegative reports. The two-sided AMM clinching mechanism terminates (an outcome exists), and every outcome is exact-settlement feasible and individually rational (the profile read as truthful). Specifically, when sell-$Y$ is dominant ($D_Y\ge D_X$, $M=D_X$), the dominant identities' total allocation $X_f$ and payment $Y_f$ satisfy
--   $$X_f\ge M,\qquad Y_f=\widetilde C_M(X_f)=p_0M+C(X_f-M),\qquad 0\le X_f-M<x_0.\qquad(58)$$
--   For every reported profile, executed prices also satisfy
--   $$S_{Y,i}\ge p_0R_{X,i}\ (i\in\mathcal I_Y),\qquad R_{Y,i}\le p_0S_{X,i}\ (i\in\mathcal I_X).\qquad(59)$$
--   Thus a sell-$Y$ identity buys $X$ at prices at least $p_0$, and a sell-$X$ identity sells $X$ at prices at most $p_0$.
--
--   Differences from the source:
--   - reading: continuous evolution by the primitive conditions (16)–(18) on event-free open intervals, on which the clock and state paths are absolutely continuous → IsRun: the event procedure is applied at every clock price; off Clinch the continuous part of dx_i has no mass; a clincher stays at the water level on a right neighbourhood of every price while active; no absolute-continuity requirement on the paths; reason: event prices may accumulate (lumps of an admissible target can be dense) and, for an admissible AMM whose right marginal ask is flat on a fat Cantor set, the sole-survivor path X = Z(p) is continuous but not absolutely continuous, so a literal AC requirement would admit no run; on event-free intervals with AC paths the two formulations coincide
--   - encoding: the two-sided AMM clinching mechanism (a function of the reports) → the relation TwoSidedOutcome; the statement holds for every outcome of every completed run; reason: the run is defined by primitive conditions without a uniqueness theorem; quantifying over every run is at least as strong as the source's statement for the unique run
--   - reading: the two-sided mechanism terminates → ∃ f, TwoSidedOutcome A ids rep f (a completed run of the dominant auction exists); reason: a run is defined only through its completion
--   - encoding: individually rational (Definition 2.3, on a truthful profile) → IndivRational on every profile of valid reports, each identity read as a trader with its report as true type; reason: a truthful profile is exactly a profile in which every report is its trader's type
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §6.1, Theorem 6.3, p.28 (PDF p.30)

import Mathlib
import Definitions.Def_SybilClinch_TwoSidedOutcome
import Definitions.Def_SybilClinch_ExactSettle
import Definitions.Def_SybilClinch_IndivRational
import Definitions.Def_SybilClinch_Report_Valid

set_option autoImplicit false

open Filter Topology Set MeasureTheory

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §6.1, Theorem 6.3 (Two-sided settlement and individual rationality), printed p.28
(PDF p.30).

The two-sided mechanism terminates, is exact-settlement feasible, and is individually rational.
When sell-`Y` is dominant, `X_f ≥ M`, `Y_f = C̃_M(X_f) = p₀M + C(X_f − M)` and `0 ≤ X_f − M < x₀`
(58). For every reported profile, executed prices satisfy `S_{Y,i} ≥ p₀R_{X,i}` (`i ∈ I_Y`) and
`R_{Y,i} ≤ p₀S_{X,i}` (`i ∈ I_X`) (59).

**Formalization Note.** "Terminates" is the existence of an outcome (a completed run of the
dominant auction). `X_f`, `Y_f` are the dominant identities' total allocation and payment. Individual
rationality is stated on every profile read as truthful (each identity one trader). -/
theorem theorem_6_3 (A : AdmissibleAMM) (ids : Finset ℕ) (rep : ℕ → Report)
    (hrep : ∀ i ∈ ids, (rep i).Valid) :
    (∃ f, TwoSidedOutcome A ids rep f) ∧
    ∀ f, TwoSidedOutcome A ids rep f →
      ExactSettle A ids rep f ∧ IndivRational ids rep f ∧
      (demandX A ids rep ≤ demandY A ids rep →
        demandX A ids rep ≤ ∑ i ∈ eligY A ids rep, (f i).recv ∧
        ∑ i ∈ eligY A ids rep, (f i).sold =
          A.Ctil (demandX A ids rep) (∑ i ∈ eligY A ids rep, (f i).recv) ∧
        ∑ i ∈ eligY A ids rep, (f i).sold =
          A.p0 * demandX A ids rep + A.C (∑ i ∈ eligY A ids rep, (f i).recv - demandX A ids rep) ∧
        0 ≤ ∑ i ∈ eligY A ids rep, (f i).recv - demandX A ids rep ∧
        ∑ i ∈ eligY A ids rep, (f i).recv - demandX A ids rep < A.x0) ∧
      (∀ i ∈ ids, (rep i).dir = Dir.sellY → A.p0 * (f i).recv ≤ (f i).sold) ∧
      (∀ i ∈ ids, (rep i).dir = Dir.sellX → (f i).recv ≤ A.p0 * (f i).sold) := by sorry

end SybilClinch
