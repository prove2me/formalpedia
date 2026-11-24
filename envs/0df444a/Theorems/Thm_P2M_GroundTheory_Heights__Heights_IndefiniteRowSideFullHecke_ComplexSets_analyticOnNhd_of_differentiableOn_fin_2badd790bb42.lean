-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticOnNhd_of_differentiableOn_fin_2badd790bb42
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticOnNhd_of_differentiableOn_fin_2badd790bb42
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:50:08.496031+00:00
-- url     : https://prove2.me/theorems/43368276-5672-4a83-84d0-534a05444ede
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets analytic On Nhd of differentiable On fin 2badd790bb42: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Heck
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets analytic On Nhd of differentiable On fin 2badd790bb42 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets analytic On Nhd of differentiable On fin 2badd790bb42 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegularOffHypersurface.lean#L29-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegularOffHypersurface.lean#L29-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularOffHypersurface
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RegularLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameGraphGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegularOffHypersurface
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
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticOnNhd_of_differentiableOn_fin_2badd790bb42 {d : ℕ} {σ : Type} [Fintype σ] {U : Set (Fin d → ℂ)}
    {G : (Fin d → ℂ) → σ → ℂ} (hU : IsOpen U) (hG : DifferentiableOn ℂ G U) : AnalyticOnNhd ℂ G U := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«analyticOnNhd_of_differentiableOn_fin» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticOnNhd_of_differentiableOn_fin_2badd790bb42
