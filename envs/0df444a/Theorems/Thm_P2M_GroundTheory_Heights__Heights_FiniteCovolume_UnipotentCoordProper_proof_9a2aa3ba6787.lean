-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentCoordProper_proof_9a2aa3ba6787
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentCoordProper_proof_9a2aa3ba6787
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:13:31.397824+00:00
-- url     : https://prove2.me/theorems/48661712-33a4-5576-ac7f-c9760a09fec4
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Unipotent Coord Proper proof 9a2aa3ba6787: P2 M Ground Theory Heights  Heights Finite Covolume Unipotent Coord Proper proof 9a2aa3ba6787
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Unipotent Coord Proper proof 9a2aa3ba6787 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Unipotent Coord Proper proof 9a2aa3ba6787 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentCoordProper.lean#L78-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentCoordProper.lean#L78-L135

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StUnipotentCoordProper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHermAtPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentCoordProper
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_HermAtPlace_proof_4b36a3148377

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology
noncomputable section
open UnipotentCoordProper
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentCoordProper_proof_9a2aa3ba6787 (h : HermitianForm F E W) (v : Basis ι E W) :
    UnipotentCoordProper.Statement h v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«UnipotentCoordProper».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentCoordProper_proof_9a2aa3ba6787
