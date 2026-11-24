-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_C_zero_b41b49555e2b
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_C_zero_b41b49555e2b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:20.447261+00:00
-- url     : https://prove2.me/theorems/4c968883-a410-4035-a6c3-cb835323d711
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free is Multi Homog C zero b41b49555e2b: P2 M Ground Theory Heights  Heights Lower Bound Free is Multi Homog C zero b41b49555e2b
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free is Multi Homog C zero b41b49555e2b construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free is Multi Homog C zero b41b49555e2b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals.lean#L132-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals.lean#L132-L139

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix ComplexOrder
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K]

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_C_zero_b41b49555e2b (a : ℤ) : IsMultiHomog (C a : MRing ι) 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«isMultiHomog_C_zero» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_C_zero_b41b49555e2b
