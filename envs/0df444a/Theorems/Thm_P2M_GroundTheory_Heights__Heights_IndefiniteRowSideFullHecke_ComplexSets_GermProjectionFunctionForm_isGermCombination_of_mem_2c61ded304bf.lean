-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermProjectionFunctionForm_isGermCombination_of_mem_2c61ded304bf
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermProjectionFunctionForm_isGermCombination_of_mem_2c61ded304bf
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:21:47.950106+00:00
-- url     : https://prove2.me/theorems/ef02ac47-248a-4e5a-b941-67be1ba10ac2
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Germ Projection Function Form is Germ Combination of mem 2c61ded304bf: P2 M Ground Theory Heights  Heights Indefinite Ro
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Germ Projection Function Form is Germ Combination of mem 2c61ded304bf construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Germ Projection Function Form is Germ Combination of mem 2c61ded304bf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGermProjectionFunctionForm.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGermProjectionFunctionForm.lean#L25-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermProjectionFunctionForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeGermPrimitivePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGermProjectionFunctionForm
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
open Topology Filter PrimeGermPrimitivePresentation
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.GermProjectionFunctionForm
variable {σ : Type} [Fintype σ]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermProjectionFunctionForm_isGermCombination_of_mem_2c61ded304bf {w : σ → ℂ} {k : ℕ} (p : Fin k → (σ → ℂ) → ℂ) (u : anFun w)
    (hu : toGerm w u ∈ holGermIdeal w p) (f : (σ → ℂ) → ℂ) (hf : ∀ z, u.1 z = f z) :
    IsGermCombination w p f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«GermProjectionFunctionForm».«isGermCombination_of_mem» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermProjectionFunctionForm_isGermCombination_of_mem_2c61ded304bf
