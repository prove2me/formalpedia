-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isMultiHomog_iff_weighted_ebc17bcac6a7
-- name    : P2M_GroundTheory_Heights__Heights_Inter_isMultiHomog_iff_weighted_ebc17bcac6a7
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:26.251811+00:00
-- url     : https://prove2.me/theorems/e21ddbf7-3242-4edb-ad06-61966a51e97a
-- title:
--   P2 M Ground Theory Heights  Heights Inter is Multi Homog iff weighted ebc17bcac6a7: P2 M Ground Theory Heights  Heights Inter is Multi Homog iff weighted ebc17bcac6a7
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter is Multi Homog iff weighted ebc17bcac6a7 construction uses the P2 M Ground Theory Heights  Heights Inter is Multi Homog iff weighted ebc17bcac6a7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFFibreSum.lean#L23-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFFibreSum.lean#L23-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFFibreBij
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFFibreMult
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
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
variable {R : Type*} [CommRing R] {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_isMultiHomog_iff_weighted_ebc17bcac6a7 (f : MRingOver R ι) (a : K → ℕ) :
    IsMultiHomog f a ↔ IsWeightedHomogeneous (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)) f a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«isMultiHomog_iff_weighted» := P2M_GroundTheory_Heights__Heights_Inter_isMultiHomog_iff_weighted_ebc17bcac6a7
