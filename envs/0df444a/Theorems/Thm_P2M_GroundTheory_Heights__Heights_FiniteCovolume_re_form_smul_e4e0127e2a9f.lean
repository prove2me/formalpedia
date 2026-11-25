-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_re_form_smul_e4e0127e2a9f
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_re_form_smul_e4e0127e2a9f
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:43:49.979407+00:00
-- url     : https://prove2.me/theorems/2d2bc81e-6222-5254-ba92-67d356c8a2c5
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume re form smul e4e0127e2a9f: P2 M Ground Theory Heights  Heights Finite Covolume re form smul e4e0127e2a9f
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume re form smul e4e0127e2a9f construction uses the P2 M Ground Theory Heights  Heights Finite Covolume re form smul e4e0127e2a9f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnfoldingIntegral.lean#L36-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnfoldingIntegral.lean#L36-L42

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsUnfoldingTorus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsTorusIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PArchLatticeDiscrete
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PVecAtNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnfoldingIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal ComplexOrder
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_re_form_smul_e4e0127e2a9f (P : Matrix ι ι ℂ) (b : ℂ) (y : ι → ℂ) :
    (star (b • y) ⬝ᵥ (P *ᵥ (b • y))).re = (star y ⬝ᵥ (P *ᵥ y)).re * ‖b‖ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«re_form_smul» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_re_form_smul_e4e0127e2a9f
