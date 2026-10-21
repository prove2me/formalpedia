-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P08_same_block_implies_linked
-- name    : QAlgorithms.Papers.Independent.Support21.P08.same_block_implies_linked
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:29:40.927115+00:00
-- url     : https://prove2.me/theorems/6b155588-5b4b-4813-b660-27da00415a59
-- title:
--   Same-block cell modules are residually linked
-- statement:
--   Let $R$ be a discrete valuation domain, $K$ its fraction field, and $k=R/\mathfrak m$ its canonical residue field. Let $A_R,A_K,A_k$ be the same cellular algebra under the basis-compatible scalar extensions, with JM elements whose complete generic content sequences are injective. Write $s\approx t$ for equality of all reduced contents. Put $F_{[t]}=\sum_{u\approx t}F_u$ and let $G_{[t]}$ be its reduction after integrality. Let $\lambda\sim\mu$ mean the equivalence closure of sharing a residue class between tableaux of the two shapes. If the nonzero right cell modules $C_k(\lambda)$ and $C_k(\mu)$ belong to the same block of $A_k$, then
--
--   $$\lambda\sim\mu.$$
--
--   Same-block membership is expressed by support on a common primitive central idempotent. No converse or indecomposability of every residue-linkage component is asserted.
-- source:
--   Seminormal forms and Gram determinants for cellular algebras, arXiv:math/0604108v4, PDF p. 18, 4.6

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

/-- Corollary 4.6, PDF p.18. Only the necessary direction is asserted for
arbitrary cellular algebras. Uses corrected complete-sequence separation.
No eigenvector part of the false Proposition 4.4 is assumed. -/
theorem same_block_implies_linked
    (S : ModularSystem (R := R) (K := K) (AR := AR) (AK := AK) (T := T) B M)
    (hsep : separatesAll S.integralJM) (l m : Shape) :
    CellsSameBlock S l m → residuallyLinked S l m := by sorry

end ModularStatements

end ResidueIntegrality

end QAlgorithms.Papers.Independent.Support21.P08

end
