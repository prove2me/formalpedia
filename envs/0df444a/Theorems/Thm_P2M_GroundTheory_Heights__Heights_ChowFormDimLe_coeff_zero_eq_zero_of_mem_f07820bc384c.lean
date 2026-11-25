-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormDimLe_coeff_zero_eq_zero_of_mem_f07820bc384c
-- name    : P2M_GroundTheory_Heights__Heights_ChowFormDimLe_coeff_zero_eq_zero_of_mem_f07820bc384c
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:38:31.932802+00:00
-- url     : https://prove2.me/theorems/212f7cb9-be7d-46ee-abc5-9a5022090a8b
-- title:
--   P2 M Ground Theory Heights  Heights Chow Form Dim Le coeff zero eq zero of mem f07820bc384c: P2 M Ground Theory Heights  Heights Chow Form Dim Le coeff zero eq zero of mem f07820bc384c
-- statement:
--   The P2 M Ground Theory Heights  Heights Chow Form Dim Le coeff zero eq zero of mem f07820bc384c construction uses the P2 M Ground Theory Heights  Heights Chow Form Dim Le coeff zero eq zero of mem f07820bc384c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowFormDimLe.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowFormDimLe.lean#L14-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChowFormDim
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormDimLe
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
open GroundTheory.Heights₂.Heights.ChowFormDimLe

theorem P2M_GroundTheory_Heights__Heights_ChowFormDimLe_coeff_zero_eq_zero_of_mem_f07820bc384c {F : Type} [Field F] {n : ℕ} {I : Ideal (MvPolynomial (Fin n) F)}
    (hI : IsProjPrime I) {g : MvPolynomial (Fin n) F} (hg : g ∈ I) : coeff 0 g = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowFormDimLe».«coeff_zero_eq_zero_of_mem» := P2M_GroundTheory_Heights__Heights_ChowFormDimLe_coeff_zero_eq_zero_of_mem_f07820bc384c
