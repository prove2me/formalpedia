-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_ker_coneMapQ_958512f3981d
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_ker_coneMapQ_958512f3981d
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T02:22:52.064567+00:00
-- url     : https://prove2.me/theorems/d64ec626-f649-5559-8807-b0d56de6b5cf
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set Coord Curve Degree ker cone Map Q 958512f3981d: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Height
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set Coord Curve Degree ker cone Map Q 958512f3981d construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set Coord Curve Degree ker cone Map Q 958512f3981d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/PCoordCurveAlgebraic.lean#L41-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/PCoordCurveAlgebraic.lean#L41-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CoordCurveDegree
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveAlgebraic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 Algebra
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_ker_coneMapQ_958512f3981d {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) :
    RingHom.ker (coneMapQ y) = ReciprocityTheory.AnForm.R.extQ (mCoordIdeal y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«HeightsSet».«CoordCurveDegree».«ker_coneMapQ» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_ker_coneMapQ_958512f3981d
