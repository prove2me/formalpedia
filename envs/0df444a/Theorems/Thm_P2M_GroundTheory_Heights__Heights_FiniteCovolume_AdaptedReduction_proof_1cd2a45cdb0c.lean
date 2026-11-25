-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_AdaptedReduction_proof_1cd2a45cdb0c
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_AdaptedReduction_proof_1cd2a45cdb0c
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:52:30.34541+00:00
-- url     : https://prove2.me/theorems/1f98dfa0-e8bf-44c8-bdc7-847252fc92a8
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Adapted Reduction proof 1cd2a45cdb0c: P2 M Ground Theory Heights  Heights Finite Covolume Adapted Reduction proof 1cd2a45cdb0c
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Adapted Reduction proof 1cd2a45cdb0c construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Adapted Reduction proof 1cd2a45cdb0c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PAdaptedReduction.lean#L104-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PAdaptedReduction.lean#L104-L135

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsAdaptedReduction
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsHyperbolicPairs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StLineNormalForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StComplementLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PAdaptedReduction
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
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_AdaptedReduction_proof_1cd2a45cdb0c (h : HermitianForm F E W) [FiniteDimensional E W]
    (h₁ : HyperbolicPairTransitive.Statement h) (h₂ : LineNormalForm.Statement h)
    (h₃ : ComplementLattice.Statement h) : AdaptedReduction.Statement h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«AdaptedReduction».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_AdaptedReduction_proof_1cd2a45cdb0c
