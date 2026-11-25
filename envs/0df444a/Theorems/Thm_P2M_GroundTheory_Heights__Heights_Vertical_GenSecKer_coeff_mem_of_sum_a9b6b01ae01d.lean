-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecKer_coeff_mem_of_sum_a9b6b01ae01d
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_GenSecKer_coeff_mem_of_sum_a9b6b01ae01d
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:44:55.013153+00:00
-- url     : https://prove2.me/theorems/7f32f344-c983-59fe-9e3a-ddda987c9e33
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Gen Sec Ker coeff mem of sum a9b6b01ae01d: P2 M Ground Theory Heights  Heights Vertical Gen Sec Ker coeff mem of sum a9b6b01ae01d
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Gen Sec Ker coeff mem of sum a9b6b01ae01d construction uses the P2 M Ground Theory Heights  Heights Vertical Gen Sec Ker coeff mem of sum a9b6b01ae01d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecKer.lean#L29-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecKer.lean#L29-L38

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDimStrictDrop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsGenSecKer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGenSecKer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial Cardinal
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.GenSecKer

theorem P2M_GroundTheory_Heights__Heights_Vertical_GenSecKer_coeff_mem_of_sum_a9b6b01ae01d {k L : Type*} [Field k] [Field L] [Algebra k L] (K : IntermediateField k L)
    {n : ℕ} (x c : Fin n → L) (b : L) (j₀ : Fin n) (hx : ∀ j, x j ∈ K) (hx0 : x j₀ ≠ 0)
    (hsum : ∑ j, c j * x j = b) (hb : b ∈ K) (hc : ∀ j, j ≠ j₀ → c j ∈ K) : c j₀ ∈ K := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«GenSecKer».«coeff_mem_of_sum» := P2M_GroundTheory_Heights__Heights_Vertical_GenSecKer_coeff_mem_of_sum_a9b6b01ae01d
