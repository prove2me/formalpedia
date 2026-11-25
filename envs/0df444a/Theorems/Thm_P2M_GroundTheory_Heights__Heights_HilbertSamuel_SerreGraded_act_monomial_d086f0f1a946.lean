-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_act_monomial_d086f0f1a946
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_act_monomial_d086f0f1a946
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:06.940732+00:00
-- url     : https://prove2.me/theorems/e43c7de7-9d79-4843-ba47-9dbd74ca38e9
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded act monomial d086f0f1a946: P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded act monomial d086f0f1a946
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded act monomial d086f0f1a946 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded act monomial d086f0f1a946 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PSerreGraded.lean#L55-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PSerreGraded.lean#L55-L58

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_act_monomial_d086f0f1a946 (v : Fin q →₀ ℕ) (a : ℤ) :
    act w (MvPolynomial.monomial v a) = C ((a : Ω) * ∏ j, w j ^ v j) * X ^ (∑ j, v j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«SerreGraded».«act_monomial» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_act_monomial_d086f0f1a946
