-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_Conservation_not_horizontal_d25330750319
-- name    : P2M_GroundTheory_Heights__Heights_Inter_Conservation_not_horizontal_d25330750319
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:28:01.839916+00:00
-- url     : https://prove2.me/theorems/e8617db1-f86b-4ea0-aaaf-126476a53907
-- title:
--   P2 M Ground Theory Heights  Heights Inter Conservation not horizontal d25330750319: P2 M Ground Theory Heights  Heights Inter Conservation not horizontal d25330750319
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Conservation not horizontal d25330750319 construction uses the P2 M Ground Theory Heights  Heights Inter Conservation not horizontal d25330750319 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ConservationDegreeFormOfExistence.lean#L63-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ConservationDegreeFormOfExistence.lean#L63-L68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ConservationDegreeFormOfExistence
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
open GroundTheory.Heights₂.Heights.Inter.Conservation
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_Conservation_not_horizontal_d25330750319 {P W : Ideal (MRing ι)} {p : ℕ} (hp : p.Prime) (hW : W ∈ divSupp P (C (p : ℤ))) :
    ¬ IsHorizontal W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«Conservation».«not_horizontal» := P2M_GroundTheory_Heights__Heights_Inter_Conservation_not_horizontal_d25330750319
