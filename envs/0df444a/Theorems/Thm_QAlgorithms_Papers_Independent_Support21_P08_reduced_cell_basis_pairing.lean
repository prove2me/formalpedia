-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P08_reduced_cell_basis_pairing
-- name    : QAlgorithms.Papers.Independent.Support21.P08.reduced_cell_basis_pairing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:30:05.607199+00:00
-- url     : https://prove2.me/theorems/f747600d-e600-436c-9fd0-cd3c0a94712c
-- title:
--   The reduced cell basis has residue-block pairings
-- statement:
--   Let $R$ be a discrete valuation domain, $K$ its fraction field, and $k=R/\mathfrak m$ its canonical residue field. Let $A_R,A_K,A_k$ be the same cellular algebra under the basis-compatible scalar extensions, with JM elements whose complete generic content sequences are injective. Write $s\approx t$ for equality of all reduced contents. Put $F_{[t]}=\sum_{u\approx t}F_u$ and let $G_{[t]}$ be its reduction after integrality. In the original cell module of shape $\lambda$, set $g_t=a_tG_{[t]}$. These vectors form a basis and
--
--   $$\langle g_t,g_u\rangle_\lambda=\begin{cases}\langle a_t,g_u\rangle_\lambda,&t\approx u,\\0,&t\not\approx u.\end{cases}$$
--
--   This uses the source proof's original cell-module interpretation and its valid projection identities, without assuming the false modular eigenvector claims.
-- source:
--   Seminormal forms and Gram determinants for cellular algebras, arXiv:math/0604108v4, PDF p. 18, 4.9

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P08

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Support21.P08

open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)

open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)

section ResidueIntegrality

variable {R K AR AK Shape : Type*} [CommRing R] [modularDomain : IsDomain R]

variable [modularDVR : IsDiscreteValuationRing R] [Field K] [Algebra R K] [modularFraction : IsFractionRing R K]

variable [Ring AR] [Algebra R AR] [Ring AK] [Algebra K AK] [Algebra R AK]

variable [modularTower : IsScalarTower R K AK] [Fintype Shape] [PartialOrder Shape]

variable {T : Shape → Type*} [∀ l, Fintype (T l)] [∀ l, PartialOrder (T l)]

variable {B : Type*} [Ring B] [Algebra (IsLocalRing.ResidueField R) B] {M : ℕ}

section ModularStatements

include modularDomain modularDVR modularFraction modularTower

/-- Proposition 4.9, PDF pp.18–19. The basis is a_t G_[t], as in the proof;
the pairing keeps the matching-residue mixed term, unlike false 3.12.
Uses corrected complete content-sequence separation. The projection part of
4.4 suffices; its false eigenvector assertions are not assumptions. -/
theorem reduced_cell_basis_pairing
    (S : ModularSystem (R := R) (K := K) (AR := AR) (AK := AK) (T := T) B M)
    (hsep : separatesAll S.integralJM) (l : Shape) :
    (∃ b : Module.Basis (T l) (IsLocalRing.ResidueField R) (T l → IsLocalRing.ResidueField R),
      ∀ t, b t = reducedCellVector S l t) ∧
    (∀ t u : T l,
      cellForm S.special l (reducedCellVector S l t) (reducedCellVector S l u) =
        if sameResidue S.integralJM ⟨l, t⟩ ⟨l, u⟩ then
          cellForm S.special l (cellVector l t) (reducedCellVector S l u)
        else 0) := by sorry

end ModularStatements

end ResidueIntegrality

end QAlgorithms.Papers.Independent.Support21.P08

end
