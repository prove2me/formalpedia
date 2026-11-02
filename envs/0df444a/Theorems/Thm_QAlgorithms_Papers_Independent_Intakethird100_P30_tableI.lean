-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P30_tableI
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P30.tableI
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:41:18.508561+00:00
-- url     : https://prove2.me/theorems/27f2fde6-5d17-4cd9-b8bc-da9fb9036b25
-- title:
--   II B: finite counts of inequivalent codes, Table I
-- statement:
--   For positive integers $n,m$, let $N(n,m)$ count equivalence classes of unordered sets of $m$ distinct binary words of length $n$ with no constant columns. Equivalence permits any coordinate permutation followed by XOR with one fixed word. The exact numeric entries of Table I are
--
--   $$\begin{array}{c|c|l}
--   n&m&N(n,m)\text{ in increasing order of }m\\\hline
--   2&2,3&1,1\\
--   3&2,\ldots,7&1,2,5,3,3,1\\
--   4&2,\ldots,15&1,3,13,24,47,55,73,56,50,27,19,6,4,1\\
--   5&2,\ldots,6&1,4,28,104,422\\
--   6&2,3,4&1,6,56\\
--   7&2,3&1,7\\
--   8&2,3&1,9
--   \end{array}$$
--
--   These are finite combinatorial cardinalities. No value is claimed for a dotted or shaded cell. The count uses complete group-action orbits of code sets, thereby forgetting word enumeration as well as coordinate symmetries.
-- source:
--   Numerical evidence for bound secrecy from two-way post-processing in quantum key distribution, arXiv:1612.07734v2, PDF p. 4, II B: finite counts of inequivalent codes, Table I

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P30

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J K L A B : Type}

variable [Fintype I] [Fintype J] [Fintype K] [Fintype L]

variable [Fintype A] [Fintype B]

/-- PDF p.4, Table I: exact finite combinatorial counts, not SDP estimates.
Dots and shaded cells do not occur in tableEntries. -/
theorem tableI : ∀ e ∈ tableEntries, codeClassCount e.1 e.2.1 = e.2.2 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P30

end
