-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_linearForm_coeff_single_4e0e6ad041de
-- name    : P2M_GroundTheory_Heights__Heights_linearForm_coeff_single_4e0e6ad041de
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:48:06.091829+00:00
-- url     : https://prove2.me/theorems/bf5c2ee6-9f23-4035-992c-0cf05ad0dd8d
-- title:
--   P2 M Ground Theory Heights  Heights linear Form coeff single 4e0e6ad041de: P2 M Ground Theory Heights  Heights linear Form coeff single 4e0e6ad041de
-- statement:
--   The P2 M Ground Theory Heights  Heights linear Form coeff single 4e0e6ad041de construction uses the P2 M Ground Theory Heights  Heights linear Form coeff single 4e0e6ad041de property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PLinearFormPrime.lean#L11-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PLinearFormPrime.lean#L11-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsNormForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PLinearFormPrime
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

theorem P2M_GroundTheory_Heights__Heights_linearForm_coeff_single_4e0e6ad041de {F : Type} [Field F] {n : ℕ} (a : Fin n → F) (i : Fin n) :
    (∑ m, X m * C (a m) : MvPolynomial (Fin n) F).coeff (Finsupp.single i 1) = a i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«linearForm_coeff_single» := P2M_GroundTheory_Heights__Heights_linearForm_coeff_single_4e0e6ad041de
