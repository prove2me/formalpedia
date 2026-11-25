-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_VectorOrbitsFinite_proof_a256cbf4870a
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_VectorOrbitsFinite_proof_a256cbf4870a
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T06:00:16.819561+00:00
-- url     : https://prove2.me/theorems/e5afcf77-4832-48f2-9b4b-f109986be224
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Vector Orbits Finite proof a256cbf4870a: P2 M Ground Theory Heights  Heights Finite Covolume Vector Orbits Finite proof a256cbf4870a
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Vector Orbits Finite proof a256cbf4870a construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Vector Orbits Finite proof a256cbf4870a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PVectorOrbitsFinite.lean#L127-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PVectorOrbitsFinite.lean#L127-L173

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsLineIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PCongruenceUnitsFiniteIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PVectorOrbitsFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_CongruenceUnitsFiniteIndex_proof_eec00df32b44

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
variable {W : Type*} [AddCommGroup W] [Module E W]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_VectorOrbitsFinite_proof_a256cbf4870a (h : HermitianForm F E W) [FiniteDimensional E W]
    (h₁ : LinePairOrbitsFinite.Statement h) (h₂ : IsotropicScaling.Statement h)
    (h₃ : BoundedIndexSubgroupsFinite.Statement W) (h₅ : LineIndexNeZero.Statement E W) :
    VectorOrbitsFinite.Statement h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«VectorOrbitsFinite».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_VectorOrbitsFinite_proof_a256cbf4870a
