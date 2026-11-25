-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_homog_C_5ce2a68ac976
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_homog_C_5ce2a68ac976
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:23:40.138929+00:00
-- url     : https://prove2.me/theorems/f055a2c9-40a1-422f-9962-b266a6051242
-- title:
--   P2 M Ground Theory Heights  Heights Inter Plucker Relations homog C 5ce2a68ac976: P2 M Ground Theory Heights  Heights Inter Plucker Relations homog C 5ce2a68ac976
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Plucker Relations homog C 5ce2a68ac976 construction uses the P2 M Ground Theory Heights  Heights Inter Plucker Relations homog C 5ce2a68ac976 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerRel.lean#L31-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerRel.lean#L31-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerRel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerRel
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.PluckerRelations
variable {K : Type*} [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_homog_C_5ce2a68ac976 (r : ℤ) (b : K) : IsMultiHomog (C r : MRing ι) (Pi.single b 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PluckerRelations».«homog_C» := P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_homog_C_5ce2a68ac976
