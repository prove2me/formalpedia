-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentCocompact_proof_f616c70de93d
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentCocompact_proof_f616c70de93d
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:13:24.829832+00:00
-- url     : https://prove2.me/theorems/5537345e-9c68-55b2-b536-6ebc5da78996
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Unipotent Cocompact proof f616c70de93d: P2 M Ground Theory Heights  Heights Finite Covolume Unipotent Cocompact proof f616c70de93d
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Unipotent Cocompact proof f616c70de93d construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Unipotent Cocompact proof f616c70de93d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentCocompact.lean#L16-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentCocompact.lean#L16-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StUnipotentHorizontal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StUnipotentCentral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PWittPartner
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentCocompact
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_WittPartner_proof_a6df1f660009

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
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentCocompact_proof_f616c70de93d (h : HermitianForm F E W) (v : Basis ι E W)
    (hP : UnipotentCoordProper.Statement h v) (hH : UnipotentHorizontal.Statement h v)
    (hC : UnipotentCentral.Statement h v) : UnipotentCocompact.Statement h v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«UnipotentCocompact».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentCocompact_proof_f616c70de93d
