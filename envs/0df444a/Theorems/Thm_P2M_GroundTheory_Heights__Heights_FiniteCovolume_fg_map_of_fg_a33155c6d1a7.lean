-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_fg_map_of_fg_a33155c6d1a7
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_fg_map_of_fg_a33155c6d1a7
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:34:01.297109+00:00
-- url     : https://prove2.me/theorems/a9d16df8-4205-4d4f-b26b-548902efb66c
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume fg map of fg a33155c6d1a7: P2 M Ground Theory Heights  Heights Finite Covolume fg map of fg a33155c6d1a7
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume fg map of fg a33155c6d1a7 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume fg map of fg a33155c6d1a7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLinePairOrbitsFinite.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLinePairOrbitsFinite.lean#L18-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsComplementExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsAdaptedReduction
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLinePairOrbitsFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
open scoped Pointwise
noncomputable section
universe u
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_fg_map_of_fg_a33155c6d1a7 {H : AddSubgroup A} (hH : H.FG) (φ : A →+ B) : (H.map φ).FG := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«fg_map_of_fg» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_fg_map_of_fg_a33155c6d1a7
