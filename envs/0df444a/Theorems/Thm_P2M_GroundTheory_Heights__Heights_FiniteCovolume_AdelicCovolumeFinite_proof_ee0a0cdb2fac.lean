-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_AdelicCovolumeFinite_proof_ee0a0cdb2fac
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_AdelicCovolumeFinite_proof_ee0a0cdb2fac
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T02:57:07.505722+00:00
-- url     : https://prove2.me/theorems/46401cb6-4c22-4b37-843a-a46799e8b0fb
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Adelic Covolume Finite proof ee0a0cdb2fac: P2 M Ground Theory Heights  Heights Finite Covolume Adelic Covolume Finite proof ee0a0cdb2fac
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Adelic Covolume Finite proof ee0a0cdb2fac construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Adelic Covolume Finite proof ee0a0cdb2fac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PAdelicCovolumeFinite.lean#L44-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PAdelicCovolumeFinite.lean#L44-L115

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsDoubleCoset
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsAdelicLattices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PAdelicCovolumeFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory IsDedekindDomain
open scoped Pointwise ComplexOrder ENNReal NumberField.AdeleRing
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_AdelicCovolumeFinite_proof_ee0a0cdb2fac (h : HermitianForm F E W) (v : Basis ι E W)
    [FiniteDimensional E W] (h₁ : LatticeOrbitsFinite.Statement h)
    (h₂ : ArithmeticCovolumeFinite.Statement h v) (h₃ : ArchimedeanUnitaryEquiv.Statement h v)
    (h₄ : AdelicLatticeDictionary.Statement h v)
    (h₅ : DoubleCosetCovolume.Statement (unitaryPoints F E (gram h.toSesq v) 𝔸[F])
      (archUnitary h v) (unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F))) :
    AdelicCovolumeFinite.Statement h v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«AdelicCovolumeFinite».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_AdelicCovolumeFinite_proof_ee0a0cdb2fac
