-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P08_residue_projector_integral
-- name    : QAlgorithms.Papers.Independent.Support21.P08.residue_projector_integral
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:29:20.68848+00:00
-- url     : https://prove2.me/theorems/d7cfa6f2-a6fd-4387-85e7-bea3bc6b804a
-- title:
--   Generic residue-class sums are integral idempotents
-- statement:
--   Let $R$ be a discrete valuation domain, $K$ its fraction field, and $k=R/\mathfrak m$ its canonical residue field. Let $A_R,A_K,A_k$ be the same cellular algebra under the basis-compatible scalar extensions, with JM elements whose complete generic content sequences are injective. Write $s\approx t$ for equality of all reduced contents. Put $F_{[t]}=\sum_{u\approx t}F_u$ and let $G_{[t]}$ be its reduction after integrality. For every residue class $[t]$,
--
--   $$F_{[t]}\in A_R,\qquad F_{[t]}^2=F_{[t]}.$$
--
--   Both integrality and idempotence are conclusions. Only unequal residues force unit differences in the DVR; distinct generic contents may have nonunit difference.
-- source:
--   Seminormal forms and Gram determinants for cellular algebras, arXiv:math/0604108v4, PDF p. 15, 4.2

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

include modularDomain modularDVR modularFraction modularTower in
/-- Lemma 4.2, PDF pp.15–16. Integrality is a conclusion, not a hypothesis.
The DVR supplies the unit-difference property for DISTINCT RESIDUES (the
overbars on p.15 have been checked in the PDF). Complete content-sequence
separation is the proof-intended correction of Definition 2.8. -/
theorem residue_projector_integral
    (DR : CellDatum (R := R) (A := AR) (T := T))
    (DK : CellDatum (R := K) (A := AK) (T := T))
    {M : ℕ} (JR : JMFamily DR M) (JK : JMFamily DK M)
    (inc : AR →ₐ[R] AK)
    (hbasis : ∀ z, inc (DR.basis z) = DK.basis z)
    (hL : ∀ i, inc (JR.L i) = JK.L i)
    (hc : ∀ t i, algebraMap R K (JR.content t i) = JK.content t i)
    (hsep : separatesAll JR) (t : CellTableau Shape T) :
    ∃ e : AR, e * e = e ∧
      inc e = ∑ s ∈ Finset.univ.filter (sameResidue JR t), jmSpectralProjector JK s := by sorry

end ResidueIntegrality

end QAlgorithms.Papers.Independent.Support21.P08

end
