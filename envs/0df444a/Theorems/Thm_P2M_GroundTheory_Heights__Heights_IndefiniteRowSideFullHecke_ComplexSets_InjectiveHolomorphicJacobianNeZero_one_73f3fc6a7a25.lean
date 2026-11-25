-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InjectiveHolomorphicJacobianNeZero_one_73f3fc6a7a25
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InjectiveHolomorphicJacobianNeZero_one_73f3fc6a7a25
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:20:27.219543+00:00
-- url     : https://prove2.me/theorems/69dff88c-ea95-41e1-a4fe-ccadaccd3a48
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Injective Holomorphic Jacobian Ne Zero one 73f3fc6a7a25: P2 M Ground Theory Heights  Heights Indefinite Row Side Full He
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Injective Holomorphic Jacobian Ne Zero one 73f3fc6a7a25 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Injective Holomorphic Jacobian Ne Zero one 73f3fc6a7a25 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PInjectiveHolomorphicJacobianNeZero.lean#L24-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PInjectiveHolomorphicJacobianNeZero.lean#L24-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StInjectiveHolomorphicJacobianNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PInjectiveHolomorphicDerivNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicKernelFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCriticalFlatNotInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PInjectiveHolomorphicJacobianNeZero
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
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicJacobianNeZero

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InjectiveHolomorphicJacobianNeZero_one_73f3fc6a7a25 {U : Set (Fin 1 → ℂ)} {f : (Fin 1 → ℂ) → Fin 1 → ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hinj : Set.InjOn f U) {x : Fin 1 → ℂ} (hx : x ∈ U) :
    LinearMap.det (fderiv ℂ f x : (Fin 1 → ℂ) →ₗ[ℂ] Fin 1 → ℂ) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«InjectiveHolomorphicJacobianNeZero».«one» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InjectiveHolomorphicJacobianNeZero_one_73f3fc6a7a25
