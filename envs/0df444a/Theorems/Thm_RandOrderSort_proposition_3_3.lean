-- Prove2me | Theorems.Thm_RandOrderSort_proposition_3_3
-- name    : RandOrderSort.proposition_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:05:37.454975+00:00
-- url     : https://prove2.me/theorems/48363525-1ded-4a89-840d-77f0190c8eda
-- title:
--   Proposition 3.3 — EmpiricalSort runs in $O(n\log n)$ time and $O(n)$ space
-- statement:
--   Given its tie priorities, EmpiricalSort can be implemented using $O(n\log n)$ comparisons and word operations and $O(n)$ auxiliary words: one program of the online comparison word-RAM makes exactly EmpiricalSort's placements for every $n\ge 2$, with words of $O(\log n)$ bits.
--
--   This is the implementation clause of Theorem 1.1, for the specific algorithm.
--
--   Differences from the source:
--   - encoding: O(n log n) comparisons and word operations and O(n) auxiliary words → `ImplementsFast`: one program on the online comparison word-RAM, words of c(⌊log₂ n⌋+1) bits, at most Cn(⌊log₂ n⌋+1) steps, at most Cn written memory cells; reason: the paper's cost model (pp.4, 18) as a machine; comparisons are steps, and for n ≥ 2 these bounds are exactly O(n log n) and O(n)
-- source:
--   Kang, Fan, Optimal High Probability Bounds for Random Order Online Sorting, arXiv:2610.15438 (version of 2026-11-01), Proposition 3.3, p.18

import Mathlib
import Definitions.Def_RandOrderSort_empiricalSort
import Definitions.Def_RandOrderSort_ImplementsFast

namespace RandOrderSort

/-- **Proposition 3.3**, Kang, Fan, *Optimal High Probability Bounds for Random Order Online Sorting*, arXiv:2610.15438 (version of 2026-11-01), p.18: "Given its tie priorities, EmpiricalSort can be implemented using
O(n log n) comparisons and word operations and O(n) auxiliary words."

**Formalization Note.** `ImplementsFast` is the cost model of §3.5 (p.18) on the online comparison
word-RAM: one program for every `n ≥ 2`, words of `c(⌊log₂ n⌋ + 1)` bits, at most
`C n (⌊log₂ n⌋ + 1)` executed instructions (comparisons included), at most `C n` memory cells ever
written, and exactly the placements of EmpiricalSort. -/
theorem proposition_3_3 : ImplementsFast empiricalSort := by sorry

end RandOrderSort
