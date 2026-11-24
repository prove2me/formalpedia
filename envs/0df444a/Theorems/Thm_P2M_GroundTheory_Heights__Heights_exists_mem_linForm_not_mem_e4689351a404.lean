-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_mem_linForm_not_mem_e4689351a404
-- name    : P2M_GroundTheory_Heights__Heights_exists_mem_linForm_not_mem_e4689351a404
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:58.978137+00:00
-- url     : https://prove2.me/theorems/b8a11b6f-ce4d-4627-8b3a-32c65d6fcfd4
-- title:
--   P2 M Ground Theory Heights  Heights exists mem lin Form not mem e4689351a404: P2 M Ground Theory Heights  Heights exists mem lin Form not mem e4689351a404
-- statement:
--   The P2 M Ground Theory Heights  Heights exists mem lin Form not mem e4689351a404 construction uses the P2 M Ground Theory Heights  Heights exists mem lin Form not mem e4689351a404 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LowerBoundConditional.lean#L210-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LowerBoundConditional.lean#L210-L235

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
omit [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_exists_mem_linForm_not_mem_e4689351a404 {I : Ideal (MvPolynomial (Fin n) K)} (hI : IsRelevant I)
    {S : Set (Fin n → 𝓞 K)} (hS : Submodule.span (𝓞 K) S = ⊤) :
    ∃ s ∈ S, linForm (fun j => (s j : K)) ∉ I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_mem_linForm_not_mem» := P2M_GroundTheory_Heights__Heights_exists_mem_linForm_not_mem_e4689351a404
