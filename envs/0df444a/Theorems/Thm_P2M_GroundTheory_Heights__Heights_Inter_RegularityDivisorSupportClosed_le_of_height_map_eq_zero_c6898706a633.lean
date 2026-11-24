-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularityDivisorSupportClosed_le_of_height_map_eq_zero_c6898706a633
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RegularityDivisorSupportClosed_le_of_height_map_eq_zero_c6898706a633
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:59.263726+00:00
-- url     : https://prove2.me/theorems/2475e44e-caf0-4837-aca9-f0b15cca16e9
-- title:
--   P2 M Ground Theory Heights  Heights Inter Regularity Divisor Support Closed le of height map eq zero c6898706a633: P2 M Ground Theory Heights  Heights Inter Regularity Divisor Support Closed le of hei
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Regularity Divisor Support Closed le of height map eq zero c6898706a633 construction uses the P2 M Ground Theory Heights  Heights Inter Regularity Divisor Support Closed le of height map eq zero c6898706a633 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LeOfHeightMapEqZero.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LeOfHeightMapEqZero.lean#L12-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerMore
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LeOfHeightMapEqZero
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

theorem P2M_GroundTheory_Heights__Heights_Inter_RegularityDivisorSupportClosed_le_of_height_map_eq_zero_c6898706a633 {A : Type*} [CommRing A] {P Q : Ideal A} [P.IsPrime]
    (h : (Q.map (Ideal.Quotient.mk P)).height = 0) : Q ≤ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RegularityDivisorSupportClosed».«le_of_height_map_eq_zero» := P2M_GroundTheory_Heights__Heights_Inter_RegularityDivisorSupportClosed_le_of_height_map_eq_zero_c6898706a633
