-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_homog_X_910d45ab2133
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_homog_X_910d45ab2133
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:37.505709+00:00
-- url     : https://prove2.me/theorems/b7bb275d-0b2d-4321-9d1b-ab1c84cc3e77
-- title:
--   P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds homog X 910d45ab2133: P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds homog X 910d45ab2133
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds homog X 910d45ab2133 construction uses the P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds homog X 910d45ab2133 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/OneNotMemOfIsPrime.lean#L49-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/OneNotMemOfIsPrime.lean#L49-L65

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PrimeComplMapLeNonZeroDivisorsQuot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_OneNotMemOfIsPrime
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo IsLocalRing
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_homog_X_910d45ab2133 [DecidableEq K] (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRing ι) (Pi.single k 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regularityLocalFlat_holds».«homog_X» := P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_homog_X_910d45ab2133
