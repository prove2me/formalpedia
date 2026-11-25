-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ShortVectorIsotropic_proof_e968e09dc108
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_ShortVectorIsotropic_proof_e968e09dc108
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:42:06.609452+00:00
-- url     : https://prove2.me/theorems/3d843a95-c158-503d-bb73-de7bc9334be8
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Short Vector Isotropic proof e968e09dc108: P2 M Ground Theory Heights  Heights Finite Covolume Short Vector Isotropic proof e968e09dc108
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Short Vector Isotropic proof e968e09dc108 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Short Vector Isotropic proof e968e09dc108 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PShortVectorIsotropic.lean#L14-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PShortVectorIsotropic.lean#L14-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PShortVectorIsotropic
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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_ShortVectorIsotropic_proof_e968e09dc108 (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : HermAtPlace.Statement h v) (h₂ : GramAtData.Statement h v)
    (h₃ : ArchInvariant.Statement h v) (h₄ : MajorantBound.Statement ι)
    (h₅ : LenSq.Statement h v) (h₆ : IntegerSmallAtPlaces.Statement E) :
    ShortVectorIsotropic.Statement h v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«ShortVectorIsotropic».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_ShortVectorIsotropic_proof_e968e09dc108
