-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagPull_prod_YBlk_228ddc3d6696
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagPull_prod_YBlk_228ddc3d6696
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:28:14.170263+00:00
-- url     : https://prove2.me/theorems/48eb68aa-8d62-464c-b2a2-625ee5543be6
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diag Pull prod YBlk 228ddc3d6696: P2 M Ground Theory Heights  Heights Inter Diag Pull prod YBlk 228ddc3d6696
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diag Pull prod YBlk 228ddc3d6696 construction uses the P2 M Ground Theory Heights  Heights Inter Diag Pull prod YBlk 228ddc3d6696 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagPull.lean#L88-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagPull.lean#L88-L90

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedC
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagPull
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_prod_YBlk_e84c3fe06e16

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Inter.DiagPull

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagPull_prod_YBlk_228ddc3d6696 {M : Type*} [CommMonoid M] (f : T.YBlk → M) : ∏ b, f b = f .base * (f .det * f .line) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagPull».«prod_YBlk» := P2M_GroundTheory_Heights__Heights_Inter_DiagPull_prod_YBlk_228ddc3d6696
