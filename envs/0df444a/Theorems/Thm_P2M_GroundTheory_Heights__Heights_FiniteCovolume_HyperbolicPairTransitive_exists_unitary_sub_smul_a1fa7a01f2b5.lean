-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_HyperbolicPairTransitive_exists_unitary_sub_smul_a1fa7a01f2b5
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_HyperbolicPairTransitive_exists_unitary_sub_smul_a1fa7a01f2b5
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:30:48.354541+00:00
-- url     : https://prove2.me/theorems/eac7a306-3450-4440-b03c-2a2ffa67c9fa
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Hyperbolic Pair Transitive exists unitary sub smul a1fa7a01f2b5: P2 M Ground Theory Heights  Heights Finite Covolume Hyperbolic Pair Transitive exis
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Hyperbolic Pair Transitive exists unitary sub smul a1fa7a01f2b5 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Hyperbolic Pair Transitive exists unitary sub smul a1fa7a01f2b5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PHyperbolicPairTransitive.lean#L34-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PHyperbolicPairTransitive.lean#L34-L50

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_HyperbolicPairTransitive_exists_unitary_sub_smul_a1fa7a01f2b5 (h : HermitianForm F E W) [FiniteDimensional E W] (u : W) (β : E)
    (hβ : β ≠ 0) (hs : β + conj F E β = h.toSesq u u) :
    ∃ g : h.unitaryGroup, ∀ z, (g : W ≃ₗ[E] W) z = z - (h.toSesq u z / β) • u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«HyperbolicPairTransitive».«exists_unitary_sub_smul» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_HyperbolicPairTransitive_exists_unitary_sub_smul_a1fa7a01f2b5
