-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P01_cellularBasis_strictification
-- name    : QAlgorithms.Papers.Independent.Support21.P01.cellularBasis_strictification
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:28:20.191016+00:00
-- url     : https://prove2.me/theorems/f39cd99d-fba2-42bf-9a7c-24db09ce41ae
-- title:
--   Strictify a relaxed cellular basis when 2 is invertible
-- statement:
--   Let $R$ be a commutative integral domain in which $2$ is invertible, and write $h=2^{-1}$. Let $A$ be a unital $R$-algebra with $R$-linear algebra anti-involution $i$. Let $\Lambda$ be the finite label poset of a relaxed cellular basis $\{c^\lambda_{s,t}\}$, with finite index sets (possibly empty) $T(\lambda)$. Define
--
--   $$
--   a^\lambda_{s,t}=c^\lambda_{s,t}+h\bigl(i(c^\lambda_{t,s})-c^\lambda_{s,t}\bigr).
--   $$
--
--   The family $\{a^\lambda_{s,t}\}$ is a cellular basis for the same poset and the same index sets, and
--
--   $$
--   i(a^\lambda_{s,t})=a^\lambda_{t,s}\qquad(\lambda\in\Lambda,\ s,t\in T(\lambda)).
--   $$
--
--   Thus a relaxed cellular datum can be made strictly cellular when $2$ is invertible.
--
--   **Formalization Note** The inverse is supplied as $h\in R$ with $2h=1$. The accepted weak-basis predicate is exactly Definition 2.3; its involution axiom is a congruence modulo strictly higher cells.
-- source:
--   Cellularity and the Jones basic construction, arXiv:0906.1496v2, PDF p. 5, Remark 2.4(2): strictification when 2 is invertible

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P01

noncomputable section

open scoped TensorProduct

namespace QAlgorithms.Papers.Independent.Support21.P01

open QAlgorithms.Papers.Independent.Renew46.P16

/-- Remark 2.4(2), PDF p.5: when 2 is invertible, the explicit adjustment
is a cellular basis with exact index swapping, on the same label poset and
index sets. Finite labels and finite cell indices follow the finite-cell
interpretation used in the source's cell-chain arguments. Empty cell index
sets are allowed; the input basis has only the relaxed axiom. -/
theorem cellularBasis_strictification
    {R A L : Type*} [CommRing R] [IsDomain R] [Ring A] [Algebra R A]
    [PartialOrder L] [Finite L]
    {T : L → Type*} [∀ l, Fintype (T l)]
    (c : CellIndex L T → A) (i : A →ₗ[R] A)
    (hcell : IsWeakCellularBasis (R := R) c i)
    (half : R) (hhalf : (2 : R) * half = 1) :
    IsWeakCellularBasis (R := R) (strictifiedCellBasis c i half) i ∧
      ∀ (l : L) (s t : T l),
        i (strictifiedCellBasis c i half ⟨l, (s, t)⟩) =
          strictifiedCellBasis c i half ⟨l, (t, s)⟩ := by sorry

end QAlgorithms.Papers.Independent.Support21.P01

end
