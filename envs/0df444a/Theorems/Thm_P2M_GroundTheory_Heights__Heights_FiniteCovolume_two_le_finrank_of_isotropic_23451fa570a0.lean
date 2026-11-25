-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_two_le_finrank_of_isotropic_23451fa570a0
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_two_le_finrank_of_isotropic_23451fa570a0
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:45:27.347068+00:00
-- url     : https://prove2.me/theorems/5a20682f-6980-4d19-ad1b-0bc54ff89ea3
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume two le finrank of isotropic 23451fa570a0: P2 M Ground Theory Heights  Heights Finite Covolume two le finrank of isotropic 23451fa570a0
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume two le finrank of isotropic 23451fa570a0 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume two le finrank of isotropic 23451fa570a0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnfoldingIntegral.lean#L21-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnfoldingIntegral.lean#L21-L32

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
omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E] [Fintype ι]
  [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_two_le_finrank_of_isotropic_23451fa570a0 [FiniteDimensional E W] (h : HermitianForm F E W) {x₀ : W}
    (hne : x₀ ≠ 0) (hiso : h.toSesq x₀ x₀ = 0) : 2 ≤ finrank E W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«two_le_finrank_of_isotropic» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_two_le_finrank_of_isotropic_23451fa570a0
