-- Prove2me | Theorems.Thm_PvsNP_weighted_opposite_outputs_le_distinct_work_reads
-- name    : PvsNP.weighted_opposite_outputs_le_distinct_work_reads
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-27T03:35:57.009124+00:00
-- url     : https://prove2.me/theorems/e203af59-d091-4fb1-a36f-25c4a38c7ae1
-- title:
--   Fractional certificate bound on work cells actually read by a native multitape machine
-- statement:
--   Compare one deterministic native multitape run with finitely many initial configurations giving different newly emitted output after the same number of steps on the same input. Initial control and input-head positions agree. Work-head positions may be translated per tape and per alternative. After translation all initial cell differences lie in a finite region. Assign nonnegative weights to the alternatives so that the total weight differing at any cell is at most one. Their total weight is bounded by the number of distinct cells of the region that the reference machine actually scans during nonhalted steps.
-- source:
--   Direct native-machine proof by coupling and fractional packing, for the Prove2Me P vs NP investigation.

import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Run
import Mathlib

open Turing Turing.MultiTapeTM
open scoped NNReal

theorem PvsNP.weighted_opposite_outputs_le_distinct_work_reads {k : ℕ} {Γ Q : Type} {x : List Γ} {I : Type} [Fintype I]
    (tm : MultiTapeTM k Γ Q) (a : Cfg k Γ Q x) (b : I → Cfg k Γ Q x) (t : ℕ)
    (offset : I → Fin k → ℤ) (control : ∀ u, a.state = (b u).state)
    (input : ∀ u, a.inputPos = (b u).inputPos)
    (heads : ∀ u i, (b u).workTapePos i = a.workTapePos i + offset u i)
    (opposite : ∀ u, (tm.runFrom a t).output.drop a.output.length ≠
      (tm.runFrom (b u) t).output.drop (b u).output.length)
    (region : Finset (Fin k × ℤ)) (weight : I → ℝ≥0) [DecidableEq Γ]
    (outside : ∀ u i z, (i,z) ∉ region → a.workTapes i z = (b u).workTapes i (z+offset u i))
    (load : ∀ i z, (∑ u, if a.workTapes i z ≠ (b u).workTapes i (z+offset u i)
      then weight u else 0) ≤ 1) :
    let positions : Finset (Fin k × ℤ) :=
      (Finset.univ.filter (fun j : Fin t × Fin k => (tm.runFrom a j.1.val).state.isSome)).image
        (fun j => (j.2,(tm.runFrom a j.1.val).workTapePos j.2))
    ∑ u, weight u ≤ ((positions ∩ region).card : ℝ≥0) := by sorry
