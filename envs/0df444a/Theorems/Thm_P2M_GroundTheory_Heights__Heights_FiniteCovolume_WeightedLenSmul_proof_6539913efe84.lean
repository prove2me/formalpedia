-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_WeightedLenSmul_proof_6539913efe84
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_WeightedLenSmul_proof_6539913efe84
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:47:41.174702+00:00
-- url     : https://prove2.me/theorems/96be0982-feec-4848-9a9e-1d91c01eb421
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Weighted Len Smul proof 6539913efe84: P2 M Ground Theory Heights  Heights Finite Covolume Weighted Len Smul proof 6539913efe84
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Weighted Len Smul proof 6539913efe84 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Weighted Len Smul proof 6539913efe84 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PWeightedLenSmul.lean#L40-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PWeightedLenSmul.lean#L40-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PWeightedLenSmul
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
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_WeightedLenSmul_proof_6539913efe84 (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : LenSq.Statement h v) : WeightedLenSmul.Statement h v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«WeightedLenSmul».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_WeightedLenSmul_proof_6539913efe84
