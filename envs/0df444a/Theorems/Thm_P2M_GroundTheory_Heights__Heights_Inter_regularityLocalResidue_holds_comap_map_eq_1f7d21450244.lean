-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_comap_map_eq_1f7d21450244
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_comap_map_eq_1f7d21450244
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:34:38.656897+00:00
-- url     : https://prove2.me/theorems/ce648829-e9a1-5976-a6db-fdd9e6f0c61a
-- title:
--   P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds comap map eq 1f7d21450244: P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds comap map eq 1f7d21450244
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds comap map eq 1f7d21450244 construction uses the P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds comap map eq 1f7d21450244 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsUnitOfNumMem.lean#L68-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsUnitOfNumMem.lean#L68-L70

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

theorem P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_comap_map_eq_1f7d21450244 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Surjective f)
    (I : Ideal R) (hI : RingHom.ker f ≤ I) : (I.map f).comap f = I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regularityLocalResidue_holds».«comap_map_eq» := P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_comap_map_eq_1f7d21450244
