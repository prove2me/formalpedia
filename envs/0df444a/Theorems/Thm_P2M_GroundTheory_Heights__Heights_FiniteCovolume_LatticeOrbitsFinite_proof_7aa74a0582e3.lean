-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_LatticeOrbitsFinite_proof_7aa74a0582e3
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_LatticeOrbitsFinite_proof_7aa74a0582e3
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:45:31.857579+00:00
-- url     : https://prove2.me/theorems/ce62ecb7-d0a9-4425-943a-67c1949f184e
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Lattice Orbits Finite proof 7aa74a0582e3: P2 M Ground Theory Heights  Heights Finite Covolume Lattice Orbits Finite proof 7aa74a0582e3
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Lattice Orbits Finite proof 7aa74a0582e3 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Lattice Orbits Finite proof 7aa74a0582e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLatticeOrbitsFinite.lean#L25-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLatticeOrbitsFinite.lean#L25-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLatticeOrbitsFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
open scoped Pointwise
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_LatticeOrbitsFinite_proof_7aa74a0582e3 (h : HermitianForm F E W) (v : Basis ι E W) [FiniteDimensional E W]
    (h₁ : MahlerCompactness.Statement h v) (h₂ : MajorantExists.Statement h v)
    (h₃ : ShortVectorIsotropic.Statement h v) (h₄ : LinePairOrbitsFinite.Statement h) :
    LatticeOrbitsFinite.Statement h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«LatticeOrbitsFinite».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_LatticeOrbitsFinite_proof_7aa74a0582e3
