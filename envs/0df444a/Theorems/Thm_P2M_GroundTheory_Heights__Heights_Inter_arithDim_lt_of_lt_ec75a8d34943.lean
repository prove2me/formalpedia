-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_arithDim_lt_of_lt_ec75a8d34943
-- name    : P2M_GroundTheory_Heights__Heights_Inter_arithDim_lt_of_lt_ec75a8d34943
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:28:27.985573+00:00
-- url     : https://prove2.me/theorems/7052d3b9-a1cf-4726-9181-f37eaa3ea648
-- title:
--   P2 M Ground Theory Heights  Heights Inter arith Dim lt of lt ec75a8d34943: P2 M Ground Theory Heights  Heights Inter arith Dim lt of lt ec75a8d34943
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter arith Dim lt of lt ec75a8d34943 construction uses the P2 M Ground Theory Heights  Heights Inter arith Dim lt of lt ec75a8d34943 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFStep.lean#L39-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFStep.lean#L39-L61

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFSecRed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFVert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFIntZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFHoriz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFFibreSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFStep
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_arithDim_lt_of_lt_ec75a8d34943 {P Q : Ideal (MRing ι)} {d d₀ : ℕ} (hP : IsArithVar P d) (hQ : IsArithVar Q d₀)
    (hle : P ≤ Q) (hne : P ≠ Q) : d₀ < d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«arithDim_lt_of_lt» := P2M_GroundTheory_Heights__Heights_Inter_arithDim_lt_of_lt_ec75a8d34943
