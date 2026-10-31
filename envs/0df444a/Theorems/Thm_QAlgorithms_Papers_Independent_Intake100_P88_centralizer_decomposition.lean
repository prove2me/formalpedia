-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P88_centralizer_decomposition
-- name    : QAlgorithms.Papers.Independent.Intake100.P88.centralizer_decomposition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:43:49.061999+00:00
-- url     : https://prove2.me/theorems/5ed3c96e-0f89-4397-bc52-3a54007ad9ef
-- title:
--   Theorem 5.4: centralizer algebra and multiplicity-free bimodule decomposition
-- statement:
--   Let $A$ be a finite-dimensional unital algebra over an algebraically closed field $F$. Suppose the finite-dimensional semisimple $A$-module $M$ has a finite decomposition into pairwise nonisomorphic simple modules $S_i$ with positive multiplicities $m_i$. Write $Z=\operatorname{End}_A(M)$. Then
--
--   $$Z\cong_F\prod_i M_{m_i}(F),\qquad
--   M\cong\bigoplus_i S_i\otimes_F F^{m_i}.$$
--
--   The second isomorphism intertwines the commuting left actions of $A$ and $Z$: a centralizer element acts by its $i$th matrix block on the multiplicity coordinates of the $i$th summand. These column-space representations are simple and classify all simple $Z$-modules, with a unique index $i$ for each isomorphism class. Finite tuples of copies of $S_i$ implement the displayed tensor factors. This is the complete centralizer decomposition, including the commuting-action information.
-- source:
--   Partition Algebras, arXiv:math/0401314v2, PDF p. 41, Theorem 5.4: centralizer algebra and multiplicity-free bimodule decomposition

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P88

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P88

attribute [local instance] Classical.propDecidable

open scoped BigOperators Matrix

open QAlgorithms.Papers.Independent.Information100.P65 (hookLength)

open QAlgorithms.Papers.Independent.Renew46.P30 (TensorIndex)

universe u v w x y

/-- Centralizer structure and the full commuting-action decomposition, PDF pp.41--42,
Theorem 5.4. Finite tuples of copies of `S i` are the canonical model for
`S i ⊗ F^(mult i)`. The displayed action equation specifies both commuting actions;
the last clause classifies all simple centralizer modules, without an opposite-action error. -/
theorem centralizer_decomposition (F A M I : Type*) [Field F] [IsAlgClosed F]
    [Ring A] [Algebra F A] [FiniteDimensional F A]
    [AddCommGroup M] [Module F M] [Module A M] [IsScalarTower F A M]
    [FiniteDimensional F M] [IsSemisimpleModule A M] [Fintype I] [DecidableEq I]
    (S : I → Type*) [∀ i, AddCommGroup (S i)] [∀ i, Module F (S i)]
    [∀ i, Module A (S i)] [∀ i, IsScalarTower F A (S i)] [∀ i, IsSimpleModule A (S i)]
    (mult : I → ℕ) (_hpos : ∀ i, 0 < mult i)
    (_hdistinct : ∀ i j : I, i ≠ j → ¬ Nonempty (S i ≃ₗ[A] S j))
    (_decomp : M ≃ₗ[A] ((i : I) → Fin (mult i) → S i)) :
    ∃ e : Module.End A M ≃ₐ[F] ((i : I) → Matrix (Fin (mult i)) (Fin (mult i)) F),
      ∃ f : M ≃ₗ[A] ((i : I) → Fin (mult i) → S i),
        (∀ (z : Module.End A M) (v : M) (i : I) (j : Fin (mult i)),
          f (z v) i j = ∑ l : Fin (mult i), e z i j l • f v i l) ∧
        (∀ i : I, IrreducibleAction (F := F) (fun (z : Module.End A M) (v : Fin (mult i) → F) =>
          (e z i).mulVec v)) ∧
        (∀ (U : Type*) [AddCommGroup U] [Module F U] [Module (Module.End A M) U]
          [IsScalarTower F (Module.End A M) U] [IsSimpleModule (Module.End A M) U]
          [FiniteDimensional F U],
          ∃! i : I, ∃ q : U ≃ₗ[F] (Fin (mult i) → F),
            ∀ (z : Module.End A M) (v : U), q (z • v) = (e z i).mulVec (q v)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P88

end
