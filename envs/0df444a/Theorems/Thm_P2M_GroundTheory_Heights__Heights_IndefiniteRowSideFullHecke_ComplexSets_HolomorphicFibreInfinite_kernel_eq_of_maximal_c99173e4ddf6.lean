-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HolomorphicFibreInfinite_kernel_eq_of_maximal_c99173e4ddf6
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HolomorphicFibreInfinite_kernel_eq_of_maximal_c99173e4ddf6
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:22:14.70604+00:00
-- url     : https://prove2.me/theorems/c2f1e328-5cf2-432d-9375-d0018e9074eb
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Holomorphic Fibre Infinite kernel eq of maximal c99173e4ddf6: P2 M Ground Theory Heights  Heights Indefinite Row Side Fu
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Holomorphic Fibre Infinite kernel eq of maximal c99173e4ddf6 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Holomorphic Fibre Infinite kernel eq of maximal c99173e4ddf6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHolomorphicFibreInfinite.lean#L14-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHolomorphicFibreInfinite.lean#L14-L35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicFibreInfinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PImplicitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHolomorphicFibreInfinite
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
open Topology Metric
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.HolomorphicFibreInfinite

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HolomorphicFibreInfinite_kernel_eq_of_maximal_c99173e4ddf6 {k d r : ℕ} (A : (Fin k → ℂ) →L[ℂ] (Fin d → ℂ)) (v : Fin r → Fin k → ℂ)
    (Λ : (Fin d → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (hmax : ∀ u : Fin (r + 1) → Fin k → ℂ, ¬ LinearIndependent ℂ (fun j => A (u j)))
    (hind : LinearIndependent ℂ (fun j => Λ (A (v j)))) {x : Fin k → ℂ} (hx : Λ (A x) = 0) :
    A x = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«HolomorphicFibreInfinite».«kernel_eq_of_maximal» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HolomorphicFibreInfinite_kernel_eq_of_maximal_c99173e4ddf6
