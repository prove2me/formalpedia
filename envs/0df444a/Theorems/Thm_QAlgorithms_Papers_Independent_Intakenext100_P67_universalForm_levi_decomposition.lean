-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P67_universalForm_levi_decomposition
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P67.universalForm_levi_decomposition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:25:36.552598+00:00
-- url     : https://prove2.me/theorems/178f86ab-8167-4338-ac7f-585d8dcd63b9
-- title:
--   The invariant Levi decomposition of the universal coefficient space
-- statement:
--   Let $\mathfrak k$ be a finite-dimensional real Lie algebra with Levi decomposition $\mathfrak k=\mathfrak r\rtimes\mathfrak s$ and chosen decomposition $\mathfrak s\cong\bigoplus_{i=1}^r\mathfrak s_i^{m_i}$. The real simple Lie algebras $\mathfrak s_i$ are pairwise nonisomorphic and $m_i>0$. Let $V_0$ be the linear span of $\kappa_u(\mathfrak r,\mathfrak k)$ and $V_i$ the span of $\kappa_u(\mathfrak s_i^{m_i},\mathfrak s_i^{m_i})$, through their actual embeddings in $\mathfrak k$. Then
--
--   $$V(\mathfrak k)=V_0\oplus V_1\oplus\cdots\oplus V_r\cong V_0\oplus V(\mathfrak s_1)^{m_1}\oplus\cdots\oplus V(\mathfrak s_r)^{m_r}.$$
--
--   Every automorphism of $\mathfrak k$ preserves each displayed subspace. The first sum is internal: its isomorphism into $V(\mathfrak k)$ is the sum of the inclusions. This identifies canonical coefficient subspaces even though the chosen Levi complement itself need not be characteristic.
-- source:
--   Central extensions of groups of sections, arXiv:0711.3437v2, PDF p. 42, Theorem B.6

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P67

namespace QAlgorithms.Papers.Independent.Intakenext100.P67

open scoped TensorProduct

universe u v w

attribute [local instance] QAlgorithms.Papers.Independent.Intakenext100.P67.dependentLieRing

attribute [local instance] QAlgorithms.Papers.Independent.Intakenext100.P67.dependentLieAlgebra

section LeviDecomposition

variable (L : Type u) [LieRing L] [LieAlgebra ℝ L]

/-- Theorem B.6, PDF pp. 42–43: the radical image and each semisimple
isotypic image form an internal direct sum in V(L), with the stated factor
isomorphisms, invariant under every automorphism of L. Only their images
are asserted invariant; the chosen Levi complement itself need not be.
Finite products model the source's finite direct sums, including r = 0. -/
theorem universalForm_levi_decomposition [FiniteDimensional ℝ L]
    {r : ℕ} (s : LieSubalgebra ℝ L)
    (hs : LieAlgebra.IsSemisimple ℝ s)
    (hcompl : IsCompl (LieAlgebra.radical ℝ L).toSubmodule s.toSubmodule)
    (S : Fin r → Type v) [∀ i, LieRing (S i)] [∀ i, LieAlgebra ℝ (S i)]
    [∀ i, FiniteDimensional ℝ (S i)]
    (hSimple : ∀ i, LieAlgebra.IsSimple ℝ (S i))
    (hDistinct : ∀ i j, i ≠ j → IsEmpty (S i ≃ₗ⁅ℝ⁆ S j))
    (m : Fin r → ℕ) (hm : ∀ i, 0 < m i)
    (e : s ≃ₗ⁅ℝ⁆ ((i : Fin r) → Fin (m i) → S i)) :
    let V0 := universalFormSpan L (LieAlgebra.radical ℝ L).toSubmodule ⊤
    let Vi := fun i => universalFormSpan L
      (leviIsotypicSubspace L s S m e i) (leviIsotypicSubspace L s S m e i)
    (∃ eV : UniversalFormSpace L ≃ₗ[ℝ] (V0 × ((i : Fin r) → Vi i)),
      ∀ v : V0 × ((i : Fin r) → Vi i),
        eV.symm v = (v.1 : UniversalFormSpace L) +
          ∑ i : Fin r, (v.2 i : UniversalFormSpace L)) ∧
    (∀ i, Nonempty ((Vi i) ≃ₗ[ℝ] (Fin (m i) → UniversalFormSpace (S i)))) ∧
    (∀ a : L ≃ₗ⁅ℝ⁆ L,
      (∀ v ∈ V0, universalMap a.toLieHom v ∈ V0) ∧
      (∀ i v, v ∈ Vi i → universalMap a.toLieHom v ∈ Vi i)) := by sorry

end LeviDecomposition

end QAlgorithms.Papers.Independent.Intakenext100.P67
