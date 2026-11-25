-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsChowForm_incIdeal_eq_span_e2f6b622f525
-- name    : P2M_GroundTheory_Heights__Heights_IsChowForm_incIdeal_eq_span_e2f6b622f525
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:44:58.564443+00:00
-- url     : https://prove2.me/theorems/09df463c-ed8c-4df4-aa08-51d580f019f8
-- title:
--   P2 M Ground Theory Heights  Heights Is Chow Form inc Ideal eq span e2f6b622f525: P2 M Ground Theory Heights  Heights Is Chow Form inc Ideal eq span e2f6b622f525
-- statement:
--   The P2 M Ground Theory Heights  Heights Is Chow Form inc Ideal eq span e2f6b622f525 construction uses the P2 M Ground Theory Heights  Heights Is Chow Form inc Ideal eq span e2f6b622f525 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PConeDimOfChowForm.lean#L10-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PConeDimOfChowForm.lean#L10-L15

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PConeDimOfChowForm
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

theorem P2M_GroundTheory_Heights__Heights_IsChowForm_incIdeal_eq_span_e2f6b622f525 {F : Type*} [Field F] {n k : ℕ}
    {P : Ideal (MvPolynomial (Fin n) F)} {f : MvPolynomial (Fin k × Fin n) F}
    (hf : IsChowForm P k f) : incIdeal P k = Ideal.span {f} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IsChowForm».«incIdeal_eq_span» := P2M_GroundTheory_Heights__Heights_IsChowForm_incIdeal_eq_span_e2f6b622f525
