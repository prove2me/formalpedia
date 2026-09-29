-- Prove2me | Theorems.Thm_WeierstrassProjModel_negMor_over
-- name    : WeierstrassProjModel.negMor_over
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/7fe58c78-fa84-5954-bb19-599e3323eb4b
-- title:
--   Negation on the projective Weierstrass model is a Spec R-morphism
-- statement:
--   Let $R$ be a commutative ring and let $W$ be a Weierstrass curve over $R$, with associated projective Weierstrass data $W.\mathrm{toProjective}$. Write $E = \mathrm{Proj}$ of the grading `projModelGradingCR W.toProjective`, i.e. the quotient grading induced on `ProjModelRingCR W.toProjective` by the homogeneous submodules of $R[X_0,X_1,X_2]$ (indexed by `Fin 3`) modulo the homogeneous ideal `projModelHomogeneousIdealCR` of the projective Weierstrass cubic. Its structure morphism `projModelStrCR W.toProjective` is the composite of the canonical map $\mathrm{Proj} \to \mathrm{Spec}$ of the degree-zero piece, `Proj.toSpecZero`, followed by `Spec.map` of the $R$-algebra structure map $R \to (\text{degree-}0\text{ piece})$. The negation morphism `kw_lrAddNegDiag_negMor W` is the morphism $E \to E$ obtained by applying `Proj.map` to the graded ring endomorphism `kw_lrAddNegDiag_negGradedHom W` of this grading, together with the hypothesis `kw_lrAddNegDiag_negGradedHom_irrelevant_le W` that the irrelevant ideal is contained in its image. The theorem asserts the equality of morphisms: `kw_lrAddNegDiag_negMor W` followed by `projModelStrCR W.toProjective` equals `projModelStrCR W.toProjective`. No smoothness, integrality or non-degeneracy assumption on $W$ is imposed.
--
--   This records that negation on the projective plane Weierstrass model is a morphism over the base, so that it is a candidate for the inverse map of a relative group law. It is used in the construction and verification of the relative group law on the projective Weierstrass model, in particular in the identification of the inverse of a section with its composite with the negation morphism and in the computation of the product of a point with its negation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_negMor_over.lean

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.negMor_over {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) :
    kw_lrAddNegDiag_negMor W ≫ projModelStrCR W.toProjective
      = projModelStrCR W.toProjective := by sorry
