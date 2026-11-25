-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RueckertNullstellensatz_mem_holGermIdeal_of_eq_94136d4050ff
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RueckertNullstellensatz_mem_holGermIdeal_of_eq_94136d4050ff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:20:41.126306+00:00
-- url     : https://prove2.me/theorems/26c335ec-c355-486c-ae22-719d2155668e
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Rueckert Nullstellensatz mem hol Germ Ideal of eq 94136d4050ff: P2 M Ground Theory Heights  Heights Indefinite Row Side
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Rueckert Nullstellensatz mem hol Germ Ideal of eq 94136d4050ff construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Rueckert Nullstellensatz mem hol Germ Ideal of eq 94136d4050ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRueckertNullstellensatz.lean#L51-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRueckertNullstellensatz.lean#L51-L66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRueckertNullstellensatz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermsNoetherian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermNullstellensatz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRueckertNullstellensatz
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
open Topology Filter
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RueckertNullstellensatz
variable {σ : Type} [Fintype σ] {w : σ → ℂ}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RueckertNullstellensatz_mem_holGermIdeal_of_eq_94136d4050ff {k : ℕ} {p : Fin k → (σ → ℂ) → ℂ} (hp : ∀ i, AnalyticAt ℂ (p i) w)
    {h : Fin k → (σ → ℂ) → ℂ} (hh : ∀ i, AnalyticAt ℂ (h i) w) (φ : holGerms w)
    (hφ : (φ : Germ (𝓝 w) ℂ) = ((fun z => ∑ i, h i z * p i z : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ)) :
    φ ∈ holGermIdeal w p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«RueckertNullstellensatz».«mem_holGermIdeal_of_eq» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RueckertNullstellensatz_mem_holGermIdeal_of_eq_94136d4050ff
