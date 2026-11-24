-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_eval_ne_zero_of_isOpen_pi_53a6727c2b58
-- name    : P2M_GroundTheory_Heights__Heights_exists_eval_ne_zero_of_isOpen_pi_53a6727c2b58
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:34:01.455068+00:00
-- url     : https://prove2.me/theorems/7804a02c-b1ce-4d52-aa81-6a3ab9739dd7
-- title:
--   P2 M Ground Theory Heights  Heights exists eval ne zero of is Open pi 53a6727c2b58: P2 M Ground Theory Heights  Heights exists eval ne zero of is Open pi 53a6727c2b58
-- statement:
--   The P2 M Ground Theory Heights  Heights exists eval ne zero of is Open pi 53a6727c2b58 construction uses the P2 M Ground Theory Heights  Heights exists eval ne zero of is Open pi 53a6727c2b58 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceReducedAway.lean#L12-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceReducedAway.lean#L12-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceReducedAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceReducedAwayZariski
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceReducedAway
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Matrix
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_exists_eval_ne_zero_of_isOpen_pi_53a6727c2b58 {σ : Type*} [Finite σ] {F : MvPolynomial σ ℂ} (hF : F ≠ 0)
    {S : Set (σ → ℂ)} (hS : IsOpen S) (hne : S.Nonempty) : ∃ y ∈ S, eval y F ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_eval_ne_zero_of_isOpen_pi» := P2M_GroundTheory_Heights__Heights_exists_eval_ne_zero_of_isOpen_pi_53a6727c2b58
