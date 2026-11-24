-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_coe_chartMap_8edc370776b7
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_coe_chartMap_8edc370776b7
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:25.486416+00:00
-- url     : https://prove2.me/theorems/44bf50de-af80-49e1-a3e7-e44382c859cf
-- title:
--   P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds coe chart Map 8edc370776b7: P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds coe chart Map 8edc370776b7
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds coe chart Map 8edc370776b7 construction uses the P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds coe chart Map 8edc370776b7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsUnitOfNumMem.lean#L202-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsUnitOfNumMem.lean#L202-L210

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.regularityLocalResidue_holds
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable (P : Ideal (MRing ι))
variable {P} [P.IsPrime]

theorem P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_coe_chartMap_8edc370776b7 {W : Ideal (MRing ι)} (hPW : P ≤ W) {T : ∀ k, ι k} (hT : ∀ k, (X ⟨k, T k⟩ : MRing ι) ∉ W)
    (f : MRing ι) : (chartMap hPW T hT f : FractionRing (MRing ι ⧸ P)) =
      aeval (fun p => (frHom P (X ⟨p.1, T p.1⟩))⁻¹ * frHom P (X p)) f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regularityLocalResidue_holds».«coe_chartMap» := P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_coe_chartMap_8edc370776b7
