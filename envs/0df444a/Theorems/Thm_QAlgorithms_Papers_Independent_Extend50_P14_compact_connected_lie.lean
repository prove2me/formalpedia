-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P14_compact_connected_lie
-- name    : QAlgorithms.Papers.Independent.Extend50.P14.compact_connected_lie
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:04:11.838141+00:00
-- url     : https://prove2.me/theorems/f9cc08f7-e876-424a-94d5-4eb1ce6f82f4
-- title:
--   Proposition 2: compact connected matrix Lie structure
-- statement:
--   For a finite system of n≥1 positive-dimensional sites, arbitrary on-site unitary symmetry representation and 1≤k≤n, let V_k be the algebraically generated symmetric local unitary group and h_k its generated real Lie algebra. Then V_k is a compact connected embedded matrix Lie group. Its local exponential description is
--
--   $$\exists\varepsilon>0\ \forall C^\dagger=-C,\quad\|C\|<\varepsilon\ \Longrightarrow\ (e^C\in V_k\iff C\in h_k).$$
--
--   The conclusion also records unitarity and adjoint closure. This local chart description, together with the ambient matrix exponential chart, specifies the Lie structure of the actual subgroup.
-- source:
--   Restrictions on realizable unitary operations imposed by symmetry and locality, arXiv:2003.05524v3, PDF p. 14, Proposition 2: compact connected Lie structure

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P14

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P14

open scoped Classical Matrix ComplexConjugate Matrix.Norms.Frobenius

open MeasureTheory

-- Exact accepted aliases and physical operators, without local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Advance50.P49 (onWire multiSwap)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- PDF p.14, Proposition 2: compactness and connectedness of the actual
finite-product subgroup, with its embedded Lie structure, not just its closure. -/
theorem compact_connected_lie {G : Type*} [Group G] {n : ℕ} {D : Fin n → Type*}
    [∀ j, Fintype (D j)] [∀ j, DecidableEq (D j)] [∀ j, Nonempty (D j)]
    (hn : 1 ≤ n) (r : OnSite G D) (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    CompactConnectedMatrixLieGroup (symmetricLocalGroup r.total k) (symmetricLocalLie r.total k) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P14

end
