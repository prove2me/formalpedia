-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RPositionAdd_proof_13dc38e435bf
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RPositionAdd_proof_13dc38e435bf
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:29.901987+00:00
-- url     : https://prove2.me/theorems/5a2479b7-28bd-4bfb-9fcc-d3631b311391
-- title:
--   P2 M Ground Theory Heights  Heights Inter RPosition Add proof 13dc38e435bf: P2 M Ground Theory Heights  Heights Inter RPosition Add proof 13dc38e435bf
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter RPosition Add proof 13dc38e435bf construction uses the P2 M Ground Theory Heights  Heights Inter RPosition Add proof 13dc38e435bf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRSlotAdd.lean#L134-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRSlotAdd.lean#L134-L151

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMixSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsWellDefined
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRSlotAdd
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
open Classical

theorem P2M_GroundTheory_Heights__Heights_Inter_RPositionAdd_proof_13dc38e435bf (hFF : FibreFiniteStatement) (hInt : PtsIntegrableStatement) :
    RPositionAdd.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RPositionAdd».«proof» := P2M_GroundTheory_Heights__Heights_Inter_RPositionAdd_proof_13dc38e435bf
