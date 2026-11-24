-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_vanish_one_4f1d6effb138
-- name    : P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_vanish_one_4f1d6effb138
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:57.928131+00:00
-- url     : https://prove2.me/theorems/9df53a6f-00a4-4b37-82e4-63b4932bd041
-- title:
--   P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum vanish one 4f1d6effb138: P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum vanish one 4f1d6effb138
-- statement:
--   The P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum vanish one 4f1d6effb138 construction uses the P2 M Ground Theory Heights  Heights Effective HS Jet Of Monomial Sum vanish one 4f1d6effb138 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PJetOfMonomialSum.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PJetOfMonomialSum.lean#L17-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_JetOfMonomialSumStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PJetOfMonomialSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.EffectiveHS
open GroundTheory.Heights₂.Heights.EffectiveHS.JetOfMonomialSum
open Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {x : E}

theorem P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_vanish_one_4f1d6effb138 {f : E → ℂ} (h : f x = 0) : ∀ k < 1, iteratedFDeriv ℂ k f x = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«EffectiveHS».«JetOfMonomialSum».«vanish_one» := P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_vanish_one_4f1d6effb138
