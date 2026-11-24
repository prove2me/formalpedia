-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_chowHt_zero_groups_eq_zero_bd0a7654af41
-- name    : P2M_GroundTheory_Heights__Heights_chowHt_zero_groups_eq_zero_bd0a7654af41
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:58.581172+00:00
-- url     : https://prove2.me/theorems/0214b53f-ffa9-4f0c-8ea3-0e94022e3bb6
-- title:
--   P2 M Ground Theory Heights  Heights chow Ht zero groups eq zero bd0a7654af41: P2 M Ground Theory Heights  Heights chow Ht zero groups eq zero bd0a7654af41
-- statement:
--   The P2 M Ground Theory Heights  Heights chow Ht zero groups eq zero bd0a7654af41 construction uses the P2 M Ground Theory Heights  Heights chow Ht zero groups eq zero bd0a7654af41 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LowerBoundConditional.lean#L143-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LowerBoundConditional.lean#L143-L147

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
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
open MvPolynomial MeasureTheory NumberField
noncomputable section
variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_chowHt_zero_groups_eq_zero_bd0a7654af41 (H : ArchData K n) (δ : ℕ) {g : MvPolynomial (Fin 0 × Fin n) K}
    (hg : g ≠ 0) : chowHt H 0 δ g = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«chowHt_zero_groups_eq_zero» := P2M_GroundTheory_Heights__Heights_chowHt_zero_groups_eq_zero_bd0a7654af41
