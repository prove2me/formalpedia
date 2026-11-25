-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_fg_of_le_fg_fd0431823b0a
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_fg_of_le_fg_fd0431823b0a
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:52:41.069345+00:00
-- url     : https://prove2.me/theorems/63d8a4fe-f414-5c46-9701-1ee1a17a441e
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume fg of le fg fd0431823b0a: P2 M Ground Theory Heights  Heights Finite Covolume fg of le fg fd0431823b0a
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume fg of le fg fd0431823b0a construction uses the P2 M Ground Theory Heights  Heights Finite Covolume fg of le fg fd0431823b0a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLinePairOrbitsFinite.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLinePairOrbitsFinite.lean#L23-L27

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_fg_of_le_fg_fd0431823b0a {H K : AddSubgroup A} (hHK : H ≤ K) (hK : K.FG) : H.FG := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«fg_of_le_fg» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_fg_of_le_fg_fd0431823b0a
