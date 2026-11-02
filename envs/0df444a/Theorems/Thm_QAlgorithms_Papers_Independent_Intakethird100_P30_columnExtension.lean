-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P30_columnExtension
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P30.columnExtension
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:44:18.442881+00:00
-- url     : https://prove2.me/theorems/ebc231b1-b354-460d-b8f3-9166d21a1f97
-- title:
--   III D: equivalence bound for adding one column
-- statement:
--   Let $C=(C_k)_{k\in\{0,\ldots,m-1\}}$ be a code of distinct $n$-bit words, with $n\ge1$, $m\ge2$, and no constant columns. For a column $v\in\{0,1\}^m$, let $C[v]$ be obtained by adjoining $v_k$ to word $C_k$. A change between the first and last position of the new column is a coordinate permutation. Then
--
--   $$C[v]\sim C[\overline v],\qquad Q_{C[0^m]}^*=Q_{C[1^m]}^*=Q_C^*,$$
--
--   and the number of equivalence classes represented by the nonconstant new columns satisfies
--
--   $$\#\{[C[v]]:v\text{ is nonconstant}\}\le2^{m-1}-1.$$
--
--   Further coordinate equivalences may identify different complement pairs, so this is only an upper bound. The result asserts no improvement in the threshold from any particular new column.
-- source:
--   Numerical evidence for bound secrecy from two-way post-processing in quantum key distribution, arXiv:1612.07734v2, PDF p. 7, III D: equivalence bound for adding one column

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P30

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J K L A B : Type}

variable [Fintype I] [Fintype J] [Fintype K] [Fintype L]

variable [Fintype A] [Fintype B]

/-- PDF p.7: complementary columns give equivalent codes, constant columns preserve
threshold, and at most 2^(m-1)-1 nonconstant-column equivalence classes remain. -/
theorem columnExtension {n m : ℕ} (hn : 1 ≤ n) (hm : 2 ≤ m)
    (C : Fin m → Qubits n) (hC : Function.Injective C) (hcols : NoConstantColumns C) :
    (∀ v : Fin m → Bool, CodeEquivalent (prependCodeColumn C v) (prependCodeColumn C (fun k => !(v k)))) ∧
    (∀ b : Bool, bobThreshold (prependCodeColumn C (fun _ => b)) = bobThreshold C) ∧
    (columnOrbitCandidates C).card ≤ 2 ^ (m - 1) - 1 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P30

end
