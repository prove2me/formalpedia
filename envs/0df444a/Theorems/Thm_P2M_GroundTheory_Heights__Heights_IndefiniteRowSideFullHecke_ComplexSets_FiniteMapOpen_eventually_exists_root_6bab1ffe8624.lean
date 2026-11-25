-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteMapOpen_eventually_exists_root_6bab1ffe8624
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteMapOpen_eventually_exists_root_6bab1ffe8624
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:28.605638+00:00
-- url     : https://prove2.me/theorems/ce75372b-4841-42b3-a343-3194c0b41fe2
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Finite Map Open eventually exists root 6bab1ffe8624: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Finite Map Open eventually exists root 6bab1ffe8624 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Finite Map Open eventually exists root 6bab1ffe8624 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFiniteMapOpen.lean#L25-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFiniteMapOpen.lean#L25-L55

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteMapOpen
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
open MvPolynomial Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteMapOpen_eventually_exists_root_6bab1ffe8624 {d : ℕ} {F : Polynomial (MvPolynomial (Fin d) ℂ)} (hF : F.Monic)
    {y₀ : Fin d → ℂ} {t₀ : ℂ} (h₀ : evalYT F y₀ t₀ = 0) {V : Set ℂ} (hV : V ∈ 𝓝 t₀) :
    ∀ᶠ y in 𝓝 y₀, ∃ t ∈ V, evalYT F y t = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«FiniteMapOpen».«eventually_exists_root» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteMapOpen_eventually_exists_root_6bab1ffe8624
