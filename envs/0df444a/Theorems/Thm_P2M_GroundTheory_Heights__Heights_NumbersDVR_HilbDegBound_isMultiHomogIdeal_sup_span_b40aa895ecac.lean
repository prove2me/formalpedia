-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HilbDegBound_isMultiHomogIdeal_sup_span_b40aa895ecac
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_HilbDegBound_isMultiHomogIdeal_sup_span_b40aa895ecac
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:29:28.989413+00:00
-- url     : https://prove2.me/theorems/7d32d100-230a-4704-863e-d70e94dc845b
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Hilb Deg Bound is Multi Homog Ideal sup span b40aa895ecac: P2 M Ground Theory Heights  Heights Numbers DVR Hilb Deg Bound is Multi Homog Ideal sup span
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Hilb Deg Bound is Multi Homog Ideal sup span b40aa895ecac construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Hilb Deg Bound is Multi Homog Ideal sup span b40aa895ecac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHilbDegBound.lean#L39-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHilbDegBound.lean#L39-L47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHilbDegBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.HilbDegBound
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_HilbDegBound_isMultiHomogIdeal_sup_span_b40aa895ecac {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I)
    {s : MRing ι F} {c : K → ℕ} (hs : IsMultiHomog s c) :
    IsMultiHomogIdeal (I ⊔ Ideal.span {s}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«HilbDegBound».«isMultiHomogIdeal_sup_span» := P2M_GroundTheory_Heights__Heights_NumbersDVR_HilbDegBound_isMultiHomogIdeal_sup_span_b40aa895ecac
