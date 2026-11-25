-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_HyperbolicPairTransitive_exists_unitary_of_preserves_bd77755a0330
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_HyperbolicPairTransitive_exists_unitary_of_preserves_bd77755a0330
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:50:27.022224+00:00
-- url     : https://prove2.me/theorems/08d5adf6-5387-56be-bd8b-c3c530d64ae7
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Hyperbolic Pair Transitive exists unitary of preserves bd77755a0330: P2 M Ground Theory Heights  Heights Finite Covolume Hyperbolic Pair Transitive
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Hyperbolic Pair Transitive exists unitary of preserves bd77755a0330 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Hyperbolic Pair Transitive exists unitary of preserves bd77755a0330 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PHyperbolicPairTransitive.lean#L24-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PHyperbolicPairTransitive.lean#L24-L32

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
omit [NumberField E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_HyperbolicPairTransitive_exists_unitary_of_preserves_bd77755a0330 (h : HermitianForm F E W) [FiniteDimensional E W]
    (f : W →ₗ[E] W) (hf : ∀ x y, h.toSesq (f x) (f y) = h.toSesq x y) :
    ∃ g : h.unitaryGroup, ∀ z, (g : W ≃ₗ[E] W) z = f z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«HyperbolicPairTransitive».«exists_unitary_of_preserves» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_HyperbolicPairTransitive_exists_unitary_of_preserves_bd77755a0330
