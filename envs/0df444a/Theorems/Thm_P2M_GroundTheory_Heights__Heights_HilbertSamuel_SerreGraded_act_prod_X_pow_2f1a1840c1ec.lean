-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_act_prod_X_pow_2f1a1840c1ec
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_act_prod_X_pow_2f1a1840c1ec
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:18:53.613656+00:00
-- url     : https://prove2.me/theorems/42e74566-93aa-5a59-b462-90cad63176b5
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded act prod X pow 2f1a1840c1ec: P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded act prod X pow 2f1a1840c1ec
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded act prod X pow 2f1a1840c1ec construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded act prod X pow 2f1a1840c1ec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PSerreGraded.lean#L60-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PSerreGraded.lean#L60-L62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSerreGraded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PSerreGraded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded
open Polynomial
variable {Ω : Type} [Field Ω] {q : ℕ} (w : Fin q → Ω)

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_act_prod_X_pow_2f1a1840c1ec (μ : Fin q → ℕ) :
    act w (∏ j, MvPolynomial.X j ^ μ j) = C (∏ j, w j ^ μ j) * X ^ (∑ j, μ j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«SerreGraded».«act_prod_X_pow» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_act_prod_X_pow_2f1a1840c1ec
