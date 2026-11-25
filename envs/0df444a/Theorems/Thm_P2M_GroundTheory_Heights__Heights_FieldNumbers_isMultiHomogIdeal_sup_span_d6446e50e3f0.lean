-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomogIdeal_sup_span_d6446e50e3f0
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomogIdeal_sup_span_d6446e50e3f0
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:18:08.281192+00:00
-- url     : https://prove2.me/theorems/31f707dd-e1ab-4a32-b8f5-8ba6dfc15ff8
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers is Multi Homog Ideal sup span d6446e50e3f0: P2 M Ground Theory Heights  Heights Field Numbers is Multi Homog Ideal sup span d6446e50e3f0
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers is Multi Homog Ideal sup span d6446e50e3f0 construction uses the P2 M Ground Theory Heights  Heights Field Numbers is Multi Homog Ideal sup span d6446e50e3f0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbDegreeBound.lean#L38-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbDegreeBound.lean#L38-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegreeBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbDegreeBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomogIdeal_sup_span_d6446e50e3f0 {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I)
    {s : MRing ι F} {c : K → ℕ} (hs : IsMultiHomog s c) :
    IsMultiHomogIdeal (I ⊔ Ideal.span {s}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«isMultiHomogIdeal_sup_span» := P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomogIdeal_sup_span_d6446e50e3f0
