-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_Conservation_C_not_mem_17885ec104a3
-- name    : P2M_GroundTheory_Heights__Heights_Inter_Conservation_C_not_mem_17885ec104a3
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:24:18.622438+00:00
-- url     : https://prove2.me/theorems/c996f464-73dc-42ce-a6ff-f6a4b0520a11
-- title:
--   P2 M Ground Theory Heights  Heights Inter Conservation C not mem 17885ec104a3: P2 M Ground Theory Heights  Heights Inter Conservation C not mem 17885ec104a3
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Conservation C not mem 17885ec104a3 construction uses the P2 M Ground Theory Heights  Heights Inter Conservation C not mem 17885ec104a3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ConservationDegreeFormOfExistence.lean#L34-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ConservationDegreeFormOfExistence.lean#L34-L38

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

theorem P2M_GroundTheory_Heights__Heights_Inter_Conservation_C_not_mem_17885ec104a3 {P : Ideal (MRing ι)} (hP : IsHorizontal P) {a : ℤ} (ha : a ≠ 0) : C a ∉ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«Conservation».«C_not_mem» := P2M_GroundTheory_Heights__Heights_Inter_Conservation_C_not_mem_17885ec104a3
