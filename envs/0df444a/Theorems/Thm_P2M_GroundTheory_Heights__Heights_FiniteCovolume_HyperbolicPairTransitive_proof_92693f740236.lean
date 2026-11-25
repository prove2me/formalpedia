-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_HyperbolicPairTransitive_proof_92693f740236
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_HyperbolicPairTransitive_proof_92693f740236
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:51:38.159934+00:00
-- url     : https://prove2.me/theorems/574ad77e-b608-4125-a1c3-ce6702d68f0e
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Hyperbolic Pair Transitive proof 92693f740236: P2 M Ground Theory Heights  Heights Finite Covolume Hyperbolic Pair Transitive proof 92693f740236
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Hyperbolic Pair Transitive proof 92693f740236 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Hyperbolic Pair Transitive proof 92693f740236 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PHyperbolicPairTransitive.lean#L89-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PHyperbolicPairTransitive.lean#L89-L120

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsHyperbolicPairs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHyperbolicPairTransitive
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
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
open GroundTheory.Heights₂.Heights.FiniteCovolume.HyperbolicPairTransitive

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_HyperbolicPairTransitive_proof_92693f740236 (h : HermitianForm F E W) [FiniteDimensional E W] :
    HyperbolicPairTransitive.Statement h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«HyperbolicPairTransitive».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_HyperbolicPairTransitive_proof_92693f740236
