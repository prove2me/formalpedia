-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_linear_form_hyps_b156864bfb3e
-- name    : P2M_GroundTheory_Heights__Heights_linear_form_hyps_b156864bfb3e
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:42:23.674278+00:00
-- url     : https://prove2.me/theorems/456ca896-39bd-4baf-94c2-3cdad7d5b146
-- title:
--   P2 M Ground Theory Heights  Heights linear form hyps b156864bfb3e: P2 M Ground Theory Heights  Heights linear form hyps b156864bfb3e
-- statement:
--   The P2 M Ground Theory Heights  Heights linear form hyps b156864bfb3e construction uses the P2 M Ground Theory Heights  Heights linear form hyps b156864bfb3e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/IsProbabilityMeasureSphereLaw.lean#L302-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/IsProbabilityMeasureSphereLaw.lean#L302-L307

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
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
open MvPolynomial NumberField MeasureTheory ProbabilityTheory TensorProduct ComplexAt
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_linear_form_hyps_b156864bfb3e :
    ((X 0 : MvPolynomial (Fin 1) ℂ) ≠ 0 ∧ (X 0 : MvPolynomial (Fin 1) ℂ).IsHomogeneous 1 ∧
      eval (Pi.single 0 1) (X 0 : MvPolynomial (Fin 1) ℂ) ≠ 0) ∧
    ((X 0 : MvPolynomial (Fin 2) ℂ) ≠ 0 ∧ (X 0 : MvPolynomial (Fin 2) ℂ).IsHomogeneous 1 ∧
      eval (Pi.single 0 1) (X 0 : MvPolynomial (Fin 2) ℂ) ≠ 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«linear_form_hyps» := P2M_GroundTheory_Heights__Heights_linear_form_hyps_b156864bfb3e
