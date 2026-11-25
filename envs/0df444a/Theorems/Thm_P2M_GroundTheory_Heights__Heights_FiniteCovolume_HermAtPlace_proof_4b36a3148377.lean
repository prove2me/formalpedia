-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_HermAtPlace_proof_4b36a3148377
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_HermAtPlace_proof_4b36a3148377
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:44:27.609269+00:00
-- url     : https://prove2.me/theorems/9dae5809-4b21-40f3-8598-cb1d1fb1c490
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Herm At Place proof 4b36a3148377: P2 M Ground Theory Heights  Heights Finite Covolume Herm At Place proof 4b36a3148377
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Herm At Place proof 4b36a3148377 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Herm At Place proof 4b36a3148377 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PHermAtPlace.lean#L14-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PHermAtPlace.lean#L14-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHermAtPlace
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
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_HermAtPlace_proof_4b36a3148377 (h : HermitianForm F E W) (v : Basis ι E W) :
    HermAtPlace.Statement h v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«HermAtPlace».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_HermAtPlace_proof_4b36a3148377
