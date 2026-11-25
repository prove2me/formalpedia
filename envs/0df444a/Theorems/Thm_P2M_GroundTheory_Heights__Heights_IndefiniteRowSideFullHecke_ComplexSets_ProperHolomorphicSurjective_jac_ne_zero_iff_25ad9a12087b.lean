-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ProperHolomorphicSurjective_jac_ne_zero_iff_25ad9a12087b
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ProperHolomorphicSurjective_jac_ne_zero_iff_25ad9a12087b
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:20:26.238237+00:00
-- url     : https://prove2.me/theorems/e90754af-1010-49b3-b8e3-3f2b59f834c4
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Proper Holomorphic Surjective jac ne zero iff 25ad9a12087b: P2 M Ground Theory Heights  Heights Indefinite Row Side Full
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Proper Holomorphic Surjective jac ne zero iff 25ad9a12087b construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Proper Holomorphic Surjective jac ne zero iff 25ad9a12087b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PProperHolomorphicSurjective.lean#L30-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PProperHolomorphicSurjective.lean#L30-L36

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ProperHolomorphicSurjective_jac_ne_zero_iff_25ad9a12087b {k : ℕ} (g : (Fin k → ℂ) → Fin k → ℂ) (v : Fin k → ℂ) :
    jac g v ≠ 0 ↔ Function.Injective (fderiv ℂ g v) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«ProperHolomorphicSurjective».«jac_ne_zero_iff» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ProperHolomorphicSurjective_jac_ne_zero_iff_25ad9a12087b
