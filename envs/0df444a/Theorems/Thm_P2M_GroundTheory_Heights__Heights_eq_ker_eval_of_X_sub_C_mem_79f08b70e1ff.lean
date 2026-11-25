-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_eq_ker_eval_of_X_sub_C_mem_79f08b70e1ff
-- name    : P2M_GroundTheory_Heights__Heights_eq_ker_eval_of_X_sub_C_mem_79f08b70e1ff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:46:20.459206+00:00
-- url     : https://prove2.me/theorems/7d66ac6c-42e4-431b-8946-2d4455b47c31
-- title:
--   P2 M Ground Theory Heights  Heights eq ker eval of X sub C mem 79f08b70e1ff: P2 M Ground Theory Heights  Heights eq ker eval of X sub C mem 79f08b70e1ff
-- statement:
--   The P2 M Ground Theory Heights  Heights eq ker eval of X sub C mem 79f08b70e1ff construction uses the P2 M Ground Theory Heights  Heights eq ker eval of X sub C mem 79f08b70e1ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceReducedAwayZariski.lean#L12-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceReducedAwayZariski.lean#L12-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceReducedAwayZariski
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceBundleRadicalAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceReducedAwayZariski
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
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_eq_ker_eval_of_X_sub_C_mem_79f08b70e1ff {n : ℕ} (q : Fin n → ℂ) (P : Ideal (MvPolynomial (Fin n) ℂ))
    (hP : P.IsPrime) (h : ∀ k, X k - C (q k) ∈ P) : P = RingHom.ker (eval q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«eq_ker_eval_of_X_sub_C_mem» := P2M_GroundTheory_Heights__Heights_eq_ker_eval_of_X_sub_C_mem_79f08b70e1ff
