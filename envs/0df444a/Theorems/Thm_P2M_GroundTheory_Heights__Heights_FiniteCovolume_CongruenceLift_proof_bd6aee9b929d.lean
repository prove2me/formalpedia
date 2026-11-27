-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_CongruenceLift_proof_bd6aee9b929d
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_CongruenceLift_proof_bd6aee9b929d
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:14:12.476804+00:00
-- url     : https://prove2.me/theorems/c313f05e-e04d-581a-9cda-2e7e628106ae
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Congruence Lift proof bd6aee9b929d: P2 M Ground Theory Heights  Heights Finite Covolume Congruence Lift proof bd6aee9b929d
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Congruence Lift proof bd6aee9b929d construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Congruence Lift proof bd6aee9b929d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PCongruenceLift.lean#L78-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PCongruenceLift.lean#L78-L139

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsStabilizerLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PComplementLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PComplementExtension
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsNsmulMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PCongruenceLift
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_proof_b489f5d0bce6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementLattice_proof_1c65f8cd215a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_LinePairOrbitsFinite_proof_09504d4235de

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
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_CongruenceLift_proof_bd6aee9b929d [FiniteDimensional E W] (h : HermitianForm F E W) :
    CongruenceLift.Statement h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«CongruenceLift».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_CongruenceLift_proof_bd6aee9b929d
