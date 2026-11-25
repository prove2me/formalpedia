-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_HyperbolicPairTransitive_exists_unitary_carry_1fda0d326aee
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_HyperbolicPairTransitive_exists_unitary_carry_1fda0d326aee
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:50:21.401159+00:00
-- url     : https://prove2.me/theorems/2c64e591-8415-5119-a8a5-1554e185aa63
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Hyperbolic Pair Transitive exists unitary carry 1fda0d326aee: P2 M Ground Theory Heights  Heights Finite Covolume Hyperbolic Pair Transitive exists
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Hyperbolic Pair Transitive exists unitary carry 1fda0d326aee construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Hyperbolic Pair Transitive exists unitary carry 1fda0d326aee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PHyperbolicPairTransitive.lean#L52-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PHyperbolicPairTransitive.lean#L52-L87

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_HyperbolicPairTransitive_exists_unitary_carry_1fda0d326aee (h : HermitianForm F E W) [FiniteDimensional E W] (x y c : W)
    (hxy : h.toSesq x x = h.toSesq y y) (hx : h.toSesq x x ≠ 0)
    (hxc : h.toSesq x c = 0) (hyc : h.toSesq y c = 0) :
    ∃ g : h.unitaryGroup, (g : W ≃ₗ[E] W) x = y ∧ (g : W ≃ₗ[E] W) c = c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«HyperbolicPairTransitive».«exists_unitary_carry» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_HyperbolicPairTransitive_exists_unitary_carry_1fda0d326aee
