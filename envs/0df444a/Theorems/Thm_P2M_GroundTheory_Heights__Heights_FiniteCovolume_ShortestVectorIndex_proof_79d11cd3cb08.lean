-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ShortestVectorIndex_proof_79d11cd3cb08
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_ShortestVectorIndex_proof_79d11cd3cb08
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:49:25.290973+00:00
-- url     : https://prove2.me/theorems/0d2c4de4-11bf-49df-b9c1-040d607a5768
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Shortest Vector Index proof 79d11cd3cb08: P2 M Ground Theory Heights  Heights Finite Covolume Shortest Vector Index proof 79d11cd3cb08
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Shortest Vector Index proof 79d11cd3cb08 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Shortest Vector Index proof 79d11cd3cb08 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PShortestVectorIndex.lean#L16-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PShortestVectorIndex.lean#L16-L56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PShortestVectorIndex
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
omit [IsTotallyReal F]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_ShortestVectorIndex_proof_79d11cd3cb08 (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : LineIndexCoeffs.Statement (E := E) W) (h₂ : LineCoeffsFG.Statement (E := E) W)
    (h₃ : WeightedLenSmul.Statement h v) (h₄ : WeightPos.Statement h v)
    (h₅ : WeightedIndexBound.Statement E) : ShortestVectorIndex.Statement h v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«ShortestVectorIndex».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_ShortestVectorIndex_proof_79d11cd3cb08
