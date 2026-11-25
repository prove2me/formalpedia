-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_LenSq_proof_189de68b9718
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_LenSq_proof_189de68b9718
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:43:26.78573+00:00
-- url     : https://prove2.me/theorems/23bbd20f-564d-51f4-ab87-d76f0cfe5c49
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Len Sq proof 189de68b9718: P2 M Ground Theory Heights  Heights Finite Covolume Len Sq proof 189de68b9718
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Len Sq proof 189de68b9718 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Len Sq proof 189de68b9718 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLenSq.lean#L23-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLenSq.lean#L23-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLenSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix
open scoped ComplexOrder
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_LenSq_proof_189de68b9718 (h : HermitianForm F E W) (v : Basis ι E W) : LenSq.Statement h v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«LenSq».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_LenSq_proof_189de68b9718
