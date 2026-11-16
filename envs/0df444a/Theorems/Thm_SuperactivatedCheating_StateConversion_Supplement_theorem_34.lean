-- Prove2me | Theorems.Thm_SuperactivatedCheating_StateConversion_Supplement_theorem_34
-- name    : SuperactivatedCheating.StateConversion.Supplement.theorem_34
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:27:42.740081+00:00
-- url     : https://prove2.me/theorems/0c1d2682-f601-4c22-ad16-27822a56c4f3
-- title:
--   Theorem 34 (companion theorem; not used in the proof of the goal) — zero-error assisted classical non-superactivation
-- statement:
--   Let $N_1,N_2$ be any CPTP channels between finite nonzero registers. Both zero-capacity classes are closed under tensor product:
--   $$C_{0,E}^{(1)}(N_1)=C_{0,E}^{(1)}(N_2)=0\ \Longrightarrow\ C_{0,E}^{(1)}(N_1\otimes N_2)=0,$$
--   $$C_{0,E}(N_1)=C_{0,E}(N_2)=0\ \Longrightarrow\ C_{0,E}(N_1\otimes N_2)=0.$$
--   Here the capacities are defined by actual exact assisted classical codes. For each factor the operational regularization is finite and equals the limit $\lim_{k\to\infty}C_{0,E}^{(1)}(N_i^{\otimes k})/k$; the statement includes this agreement explicitly. Thus neither one-shot nor asymptotic assisted classical zero-error capacity superactivates. No capacity additivity or generic regularization axioms are hypotheses.
--
--   Differences from the source:
--   - encoding: one-shot and asymptotic operational assisted capacities, the latter given by a limit → ℝ≥0∞ suprema over actual codes and positive block lengths, with finite-capacity and limit agreement included in the conclusion; reason: complete suprema avoid default values; agreement with the source limit is a proof obligation
--   - encoding: finite-dimensional registers and CPTP operations → finite types in Type 0 with decidable equality, coordinate matrices and the published finite normalized Kraus channel predicate; reason: every finite register and every finite-dimensional CPTP map has this representation; no dimension or rank bound is imposed
-- source:
--   Bhattacharyya, Mančinska, Zhao, Quantum interaction can superactivate cheating under parallel repetition, STOC 2027 submission #399 (October 2026), Theorem 34, p. 26.

import Definitions.Def_SuperactivatedCheating_StateConversion_Supplement_Operations

open scoped ENNReal NNReal Matrix
noncomputable section

namespace SuperactivatedCheating.StateConversion.Supplement

/-- Theorem 34, p.26: both one-shot and asymptotic tensor closure of zero capacity.
The final clause certifies the limit convention of §2.2 for this operational regularization. -/
theorem theorem_34 {A B C D : Type}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (N : Map A B) (L : Map C D) (hN : QAlgorithms.IsChannel N) (hL : QAlgorithms.IsChannel L) :
    (CE1 N = 0 → CE1 L = 0 → CE1 (tensorMap N L) = 0) ∧
    (CE0 N = 0 → CE0 L = 0 → CE0 (tensorMap N L) = 0) ∧
    (CE0 N ≠ ⊤ ∧ Filter.Tendsto
      (fun k : ℕ+ => CE1 (power N k) / (k.val : ℝ≥0∞)) Filter.atTop (nhds (CE0 N))) ∧
    (CE0 L ≠ ⊤ ∧ Filter.Tendsto
      (fun k : ℕ+ => CE1 (power L k) / (k.val : ℝ≥0∞)) Filter.atTop (nhds (CE0 L))) := by sorry

end SuperactivatedCheating.StateConversion.Supplement
