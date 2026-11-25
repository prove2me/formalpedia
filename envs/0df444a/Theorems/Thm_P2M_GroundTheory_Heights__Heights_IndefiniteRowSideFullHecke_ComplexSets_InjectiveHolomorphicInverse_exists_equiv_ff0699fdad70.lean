-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InjectiveHolomorphicInverse_exists_equiv_ff0699fdad70
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InjectiveHolomorphicInverse_exists_equiv_ff0699fdad70
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:20:31.651869+00:00
-- url     : https://prove2.me/theorems/7814cd22-ca9b-485a-9348-f3c4fcf123a8
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Injective Holomorphic Inverse exists equiv ff0699fdad70: P2 M Ground Theory Heights  Heights Indefinite Row Side Full He
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Injective Holomorphic Inverse exists equiv ff0699fdad70 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Injective Holomorphic Inverse exists equiv ff0699fdad70 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PInjectiveHolomorphicInverse.lean#L26-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PInjectiveHolomorphicInverse.lean#L26-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StInjectiveHolomorphicInverse
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StInjectiveHolomorphicJacobianNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PInjectiveHolomorphicInverse
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Filter Topology
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicInverse

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InjectiveHolomorphicInverse_exists_equiv_ff0699fdad70 (hJ : InjectiveHolomorphicJacobianNeZero.Statement) {k : ℕ} {U : Set (Fin k → ℂ)}
    {f : (Fin k → ℂ) → Fin k → ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hinj : Set.InjOn f U)
    {x : Fin k → ℂ} (hx : x ∈ U) :
    ∃ e : (Fin k → ℂ) ≃L[ℂ] (Fin k → ℂ), HasStrictFDerivAt f (e : (Fin k → ℂ) →L[ℂ] Fin k → ℂ) x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«InjectiveHolomorphicInverse».«exists_equiv» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InjectiveHolomorphicInverse_exists_equiv_ff0699fdad70
