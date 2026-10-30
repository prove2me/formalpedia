-- Prove2me | Theorems.Thm_PutermanMDP_Unichain_transient_deviation
-- name    : PutermanMDP.Unichain.transient_deviation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:31:37.93852+00:00
-- url     : https://prove2.me/theorems/6dbb9ad8-949c-405e-8dff-b6d5a3280164
-- title:
--   Lemma 8.6.4 — transient blocks of the deviation matrix
-- statement:
--   Let $d$ be an admissible rule in a finite stationary model, and suppose its transition matrix $P_d$ is unichain. Other policies need not be unichain. Partition the states into recurrent states $R_d$ and transient states $T_d$, and partition $H_d$ accordingly. Then
--   $$H_d^{RT}=0,\qquad H_d^{TT}=(I-P_d^{TT})^{-1}.$$
--   Moreover, if a vector $u$ is zero on $R_d$ and nonnegative on $T_d$, then
--   $$H_du\ge u\ge0.$$
--
--   Both inequalities are coordinatewise. This statement includes all three clauses of the source lemma and allows an empty transient set.
--
--   Differences from the source:
--   - encoding: finite nonempty state set and finite nonempty state-dependent action sets → finite types S and A, Nonempty S, and nonempty admissible finsets; reason: the union of finitely many finite action sets is finite; irrelevant action entries can be extended by zero rewards and any stochastic row
--   - encoding: P* is the Cesàro limit and H = (I − P + P*)⁻¹(I − P*) → published Cesàro limit and equivalent deviation matrix (I − P + P*)⁻¹ − P*; reason: for finite stochastic P, (I − P + P*)⁻¹P* = P*, so these are the same matrices, including periodic chains
--   - encoding: canonical recurrent/transient block matrix → entries with recurrent/transient predicates and matrices indexed by the transient subtype; reason: restriction to these indices is the same block decomposition without choosing a permutation of the state set
-- source:
--   Puterman, Markov Decision Processes, Wiley, 1994, p. 381 (PDF 397), Lemma 8.6.4, (8.6.11); proof p. 382 (PDF 398)

import Mathlib
import Definitions.Def_PutermanMDP_Unichain_PolicyData
open MarkovDecisionProcesses Matrix

namespace PutermanMDP.Unichain

/-- Lemma 8.6.4: all three clauses, including the full transient inverse. -/
theorem transient_deviation {S A : Type*} [Fintype S] [Fintype A]
    [DecidableEq S] [Nonempty S] (M : StationaryMDP S A) (d : Rule M)
    (hd : IsUnichainMatrix (transMatrix M d.val)) :
    (∀ i j, IsRecurrent (transMatrix M d.val) i →
      ¬ IsRecurrent (transMatrix M d.val) j → policyDeviation M d i j = 0) ∧
    (transientBlock (transMatrix M d.val) (policyDeviation M d) =
      transientResolvent (transMatrix M d.val)) ∧
    (∀ u : S → ℝ,
      (∀ s, IsRecurrent (transMatrix M d.val) s → u s = 0) →
      (∀ s, ¬ IsRecurrent (transMatrix M d.val) s → 0 ≤ u s) →
      ∀ s, u s ≤ (policyDeviation M d).mulVec u s ∧ 0 ≤ u s) := by sorry

end PutermanMDP.Unichain
