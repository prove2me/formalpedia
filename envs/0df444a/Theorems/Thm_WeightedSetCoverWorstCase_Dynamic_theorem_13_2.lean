-- Prove2me | Theorems.Thm_WeightedSetCoverWorstCase_Dynamic_theorem_13_2
-- name    : WeightedSetCoverWorstCase.Dynamic.theorem_13_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:30:23.34872+00:00
-- url     : https://prove2.me/theorems/8d0ba75a-ccdb-4563-99f9-91020a778bba
-- title:
--   Theorem 13.2 ([ATG+14]) — disjoint sets with $O(1)$ worst-case singleton, deletion and merge and $O(\log n)$ worst-case find
-- statement:
--   There are a deterministic program $P$ for the real RAM (rational literals, no coins) and a constant $K$ such that $P$ initializes on empty memory in finitely many steps and then, for every sequence of operations each legal when issued: a `make`, `del` or `union` call halts within $K$ steps, a `find` call halts within $K(1+\log\max(1,n))$ steps where $n$ is the number of elements currently stored, and every answer is correct — `make x` and `union h₁ h₂` return a handle different from every other live handle (the merged set may reuse $h_1$ or $h_2$), and `find x` returns the handle of the set containing $x$.
--
--   Differences from the source:
--   - encoding: a data structure for maintaining disjoint sets with the four operations → a program of the real RAM with a call protocol: operation code and arguments in integer cells −1..−3, answer in cell −10, memory kept between calls; sets are named by handles returned by the structure; reason: a data structure is a program with persistent memory; handles are how merge names its arguments
--   - generalization: a data structure (machine constants unrestricted) → the program is admissible (rational literals only) and has no coin instruction; reason: a stronger claim: such a program is in particular a deterministic data structure
--   - reading: O(log n) worst-case find → K (1 + log max(1, n)) with n the number of elements currently stored, K chosen before the operation sequence; reason: n is not specified; the current size is the reading that does not grow with deleted elements
--   - encoding: create a singleton set containing x → make x is legal whenever x is not currently stored; reason: allows re-creating a deleted element; a stronger claim than for fresh elements only
-- source:
--   Bhattacharya, Cen, Farokhnejad and Panigrahi (2026), Fully Dynamic Weighted Set Cover: Worst-Case Recourse and Update Time, STOC 2027 submission, supplied PDF sha256 28a86be41fbea2451c118c89c7385500105ced4b59ab5e66110721ebf0909337, Theorem 13.2, p. 61 (PDF 64)

import Mathlib
import Definitions.Def_DynSetCover_Instance
import Definitions.Def_WeightedSetCoverWorstCase_Dynamic_Problem
import Definitions.Def_ClusterDecomp_Machine
import Definitions.Def_WeightedSetCoverWorstCase_Dynamic_Machine

open ClusterDecomp

namespace WeightedSetCoverWorstCase.Dynamic

theorem theorem_13_2 :
    ∃ P : Program, Admissible P ∧ NoCoin P ∧ ∃ K : ℝ,
      (∃ T, HaltsWithin P (initState [] []) T) ∧
      ∀ (ops : List DSOp) (op : DSOp), DSHistLegal P ops → (dsAfter P ops).2.Legal op →
        (∃ T : ℕ,
          (T : ℝ) ≤ (match op with
            | .find _ => K * (1 + Real.log (max 1 ((dsAfter P ops).2.size : ℝ)))
            | _ => K) ∧
          HaltsWithin P (callState (dsAfter P ops).1 op.enc) T) ∧
        (dsAfter P ops).2.Correct op (dsOutput (result P (callState (dsAfter P ops).1 op.enc))) := by sorry

end WeightedSetCoverWorstCase.Dynamic
