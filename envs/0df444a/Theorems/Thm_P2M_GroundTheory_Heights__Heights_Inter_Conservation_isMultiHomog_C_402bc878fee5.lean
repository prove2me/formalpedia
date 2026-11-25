-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_Conservation_isMultiHomog_C_402bc878fee5
-- name    : P2M_GroundTheory_Heights__Heights_Inter_Conservation_isMultiHomog_C_402bc878fee5
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:29:23.978649+00:00
-- url     : https://prove2.me/theorems/78401713-46cd-5da3-8219-42712a4ea05d
-- title:
--   P2 M Ground Theory Heights  Heights Inter Conservation is Multi Homog C 402bc878fee5: P2 M Ground Theory Heights  Heights Inter Conservation is Multi Homog C 402bc878fee5
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Conservation is Multi Homog C 402bc878fee5 construction uses the P2 M Ground Theory Heights  Heights Inter Conservation is Multi Homog C 402bc878fee5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ConservationDegreeFormOfExistence.lean#L42-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ConservationDegreeFormOfExistence.lean#L42-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ConservationDegreeFormOfExistence
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isMultiHomog_C_8aa21e557757

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
omit [Fintype K]

theorem P2M_GroundTheory_Heights__Heights_Inter_Conservation_isMultiHomog_C_402bc878fee5 (a : ℤ) : IsMultiHomog (C a : MRing ι) 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«Conservation».«isMultiHomog_C» := P2M_GroundTheory_Heights__Heights_Inter_Conservation_isMultiHomog_C_402bc878fee5
