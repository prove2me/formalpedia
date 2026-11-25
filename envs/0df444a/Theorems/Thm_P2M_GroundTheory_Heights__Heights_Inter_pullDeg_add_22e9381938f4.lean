-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pullDeg_add_22e9381938f4
-- name    : P2M_GroundTheory_Heights__Heights_Inter_pullDeg_add_22e9381938f4
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:27:43.555927+00:00
-- url     : https://prove2.me/theorems/03c14243-c117-4c92-afeb-fbcdbf3b7bcf
-- title:
--   P2 M Ground Theory Heights  Heights Inter pull Deg add 22e9381938f4: P2 M Ground Theory Heights  Heights Inter pull Deg add 22e9381938f4
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter pull Deg add 22e9381938f4 construction uses the P2 M Ground Theory Heights  Heights Inter pull Deg add 22e9381938f4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/TableDegreeThreeBase.lean#L46-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/TableDegreeThreeBase.lean#L46-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogFirstCoordinate
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TableDegreeThreeBase
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]
omit [Fintype K] [Fintype K']

theorem P2M_GroundTheory_Heights__Heights_Inter_pullDeg_add_22e9381938f4 (κ : K → K') (a b : K → ℤ) : pullDeg κ (a + b) = pullDeg κ a + pullDeg κ b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«pullDeg_add» := P2M_GroundTheory_Heights__Heights_Inter_pullDeg_add_22e9381938f4
