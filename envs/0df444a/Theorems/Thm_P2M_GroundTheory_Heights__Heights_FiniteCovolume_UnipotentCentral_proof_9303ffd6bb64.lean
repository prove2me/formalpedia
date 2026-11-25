-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentCentral_proof_9303ffd6bb64
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentCentral_proof_9303ffd6bb64
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:14:07.126824+00:00
-- url     : https://prove2.me/theorems/06a005ad-a079-5f17-8666-5090c935709a
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Unipotent Central proof 9303ffd6bb64: P2 M Ground Theory Heights  Heights Finite Covolume Unipotent Central proof 9303ffd6bb64
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Unipotent Central proof 9303ffd6bb64 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Unipotent Central proof 9303ffd6bb64 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentCentral.lean#L39-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentCentral.lean#L39-L187

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StUnipotentCentral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StRationalUnipotent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StUnipRadicalOfRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StImaginaryLatticeCocompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PScalingLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHermAtPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PGramAtData
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentCentral
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GramAtData_proof_6f69e474274d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_HermAtPlace_proof_4b36a3148377
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ScalingLaw_proof_08e97b3dc7f3

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
attribute [local instance] archMulAction
open GroundTheory.Heights₂.Heights.FiniteCovolume.UnipotentCentral

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentCentral_proof_9303ffd6bb64 (h : HermitianForm F E W) (v : Basis ι E W) (h0 : RationalUnipotent.Statement h)
    (h4 : UnipRadicalOfRational.Statement h v) (h6 : ImaginaryLatticeCocompact.Statement F E) :
    UnipotentCentral.Statement h v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«UnipotentCentral».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentCentral_proof_9303ffd6bb64
