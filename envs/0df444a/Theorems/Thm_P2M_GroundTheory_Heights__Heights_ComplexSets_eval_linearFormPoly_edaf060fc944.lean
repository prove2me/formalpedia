-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_eval_linearFormPoly_edaf060fc944
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_eval_linearFormPoly_edaf060fc944
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:16:36.928706+00:00
-- url     : https://prove2.me/theorems/4f1b1df5-f706-4cf5-8614-2b772c11b2eb
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets eval linear Form Poly edaf060fc944: P2 M Ground Theory Heights  Heights Complex Sets eval linear Form Poly edaf060fc944
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets eval linear Form Poly edaf060fc944 construction uses the P2 M Ground Theory Heights  Heights Complex Sets eval linear Form Poly edaf060fc944 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericPrimitive.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericPrimitive.lean#L14-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericPrimitive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
noncomputable section
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_eval_linearFormPoly_edaf060fc944 {k : Type*} [Field k] {n : ℕ} (φ : (Fin n → k) →ₗ[k] k) (c : Fin n → k) :
    eval c (linearFormPoly φ) = φ c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«eval_linearFormPoly» := P2M_GroundTheory_Heights__Heights_ComplexSets_eval_linearFormPoly_edaf060fc944
