-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ProperHolomorphicSurjective_differentiableOn_jac_fd06ac4187c4
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ProperHolomorphicSurjective_differentiableOn_jac_fd06ac4187c4
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:20:23.782801+00:00
-- url     : https://prove2.me/theorems/132bd897-d200-4503-adcc-16268e62c8a7
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Proper Holomorphic Surjective differentiable On jac fd06ac4187c4: P2 M Ground Theory Heights  Heights Indefinite Row Sid
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Proper Holomorphic Surjective differentiable On jac fd06ac4187c4 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Proper Holomorphic Surjective differentiable On jac fd06ac4187c4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PProperHolomorphicSurjective.lean#L38-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PProperHolomorphicSurjective.lean#L38-L55

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProperHolomorphicSurjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCompactHolomorphicFibreFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRankDeficientFibreInfinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicZeroSetDimH
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHausdorffNullComplementConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProperHolomorphicSurjective
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
open Topology Metric MeasureTheory
open scoped ENNReal NNReal
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ProperHolomorphicSurjective

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ProperHolomorphicSurjective_differentiableOn_jac_fd06ac4187c4 {k : ℕ} {Ω : Set (Fin k → ℂ)} {g : (Fin k → ℂ) → Fin k → ℂ} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) : DifferentiableOn ℂ (jac g) Ω := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«ProperHolomorphicSurjective».«differentiableOn_jac» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ProperHolomorphicSurjective_differentiableOn_jac_fd06ac4187c4
