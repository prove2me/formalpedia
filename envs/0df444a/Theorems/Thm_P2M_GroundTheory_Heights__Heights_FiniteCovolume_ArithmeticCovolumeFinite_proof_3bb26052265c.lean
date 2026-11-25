-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ArithmeticCovolumeFinite_proof_3bb26052265c
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_ArithmeticCovolumeFinite_proof_3bb26052265c
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:14:55.797492+00:00
-- url     : https://prove2.me/theorems/46695297-3de0-419e-aaeb-6bce67370593
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Arithmetic Covolume Finite proof 3bb26052265c: P2 M Ground Theory Heights  Heights Finite Covolume Arithmetic Covolume Finite proof 3bb26052265c
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Arithmetic Covolume Finite proof 3bb26052265c construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Arithmetic Covolume Finite proof 3bb26052265c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PArithmeticCovolumeFinite.lean#L25-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PArithmeticCovolumeFinite.lean#L25-L130

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PArithmeticCovolumeFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_ArithmeticCovolumeFinite_proof_3bb26052265c (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : ScalingLaw.Statement h v) (h₂ : MahlerCompactness.Statement h v)
    (h₃ : ShortVectorIsotropic.Statement h v) (h₄ : ShortestVectorIndex.Statement h v)
    (h₅ : IntegralFamilyBound.Statement E) (h₆ : MajorantExists.Statement h v)
    (h₈ : ArchLatticeDiscrete.Statement h v) (h₉ : LatticePointsBelowFinite.Statement h v) :
    ArithmeticCovolumeFinite.Statement h v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«ArithmeticCovolumeFinite».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_ArithmeticCovolumeFinite_proof_3bb26052265c
