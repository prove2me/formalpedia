-- Prove2me | Theorems.Thm_RandOrderSort_lemma_4_2
-- name    : RandOrderSort.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:06:28.896668+00:00
-- url     : https://prove2.me/theorems/91e1013a-4601-4c79-be13-ea22db680d60
-- title:
--   Lemma 4.2 — top-marked subtrees
-- statement:
--   Let $n\ge 8192$. For one operation type in one phase of any execution, at most $\mathrm{cap}(v)$ requests are charged to a top-marked node $v$. If $v$ is not a leaf, one of its children locally overflows. These conclusions apply to reallocation even when the old and new partition trees are not nested.
--
--   Every internal top mark therefore comes with a local overflow witness, which is what lets the sum over actual top marks be replaced by a sum over witnesses in (22).
--
--   Differences from the source:
--   - encoding: cap(v), the initially available cells or initially unused assignment slots below v → `capNode` of the phase's prescribed capacities `phaseCap`; reason: a phase's bucket sizes after its reallocation equal its assignment capacities (Lemma 3.1)
-- source:
--   Kang, Fan, Optimal High Probability Bounds for Random Order Online Sorting, arXiv:2610.15438 (version of 2026-11-01), Lemma 4.2, p.21

import Mathlib
import Definitions.Def_RandOrderSort_empiricalSort
import Definitions.Def_RandOrderSort_Dop

namespace RandOrderSort

/-- **Lemma 4.2 (Top-marked subtrees)**, Kang, Fan, *Optimal High Probability Bounds for Random Order Online Sorting*, arXiv:2610.15438 (version of 2026-11-01), p.21: "For one operation type in one phase, at most
cap(v) requests are charged to a top-marked node v. If v is not a leaf, one of its children locally
overflows. These conclusions apply to reallocation even when the old and new partition trees are not
nested."

**Formalization Note.** Stated for every operation (arrivals and old-cell reassignments) of every
phase of every execution with `n ≥ 8192`; the operation's tree is the phase's tree and `cap` its
bucket capacities (for arrivals, the cells available at the start of the placements; for
reallocation, the assignment slots). A node `v = (h, idx)` is a leaf when `h = 0`; its children are
`(h − 1, 2 idx)` and `(h − 1, 2 idx + 1)`. -/
theorem lemma_4_2 : ∀ n, 16 * T ≤ n → ∀ (x : Fin n → ℝ) (π σ : Equiv.Perm (Fin n)),
    ∀ p < numPhases n, ∀ (arr : Bool) (v : ℕ × ℕ), TopMarked (opReqs (runOf x π σ) p arr) v →
      nCharged (opReqs (runOf x π σ) p arr) v ≤ capNode (phaseLeaves n p) (phaseCap n p) v.1 v.2 ∧
      (0 < v.1 →
        Overflows (opReqs (runOf x π σ) p arr) (phaseLeaves n p) (phaseCap n p) (v.1 - 1) (2 * v.2) ∨
        Overflows (opReqs (runOf x π σ) p arr) (phaseLeaves n p) (phaseCap n p) (v.1 - 1)
          (2 * v.2 + 1)) := by sorry

end RandOrderSort
