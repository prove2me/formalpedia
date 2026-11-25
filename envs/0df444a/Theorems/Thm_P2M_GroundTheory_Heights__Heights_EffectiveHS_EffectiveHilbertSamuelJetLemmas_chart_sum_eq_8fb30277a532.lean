-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_EffectiveHilbertSamuelJetLemmas_chart_sum_eq_8fb30277a532
-- name    : P2M_GroundTheory_Heights__Heights_EffectiveHS_EffectiveHilbertSamuelJetLemmas_chart_sum_eq_8fb30277a532
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T06:16:20.614605+00:00
-- url     : https://prove2.me/theorems/e85fdab2-be34-44bb-b17e-f1888ebf0acd
-- title:
--   P2 M Ground Theory Heights  Heights Effective HS Effective Hilbert Samuel Jet Lemmas chart sum eq 8fb30277a532: P2 M Ground Theory Heights  Heights Effective HS Effective Hilbert Samuel Jet Lemmas cha
-- statement:
--   The P2 M Ground Theory Heights  Heights Effective HS Effective Hilbert Samuel Jet Lemmas chart sum eq 8fb30277a532 construction uses the P2 M Ground Theory Heights  Heights Effective HS Effective Hilbert Samuel Jet Lemmas chart sum eq 8fb30277a532 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/AnalyticAtOfHoloOn.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/AnalyticAtOfHoloOn.lean#L18-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_SymbolExtensionProperty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_MemSectionsOfHolLineBundleEquiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_JetOfMonomialSumStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_AnalyticAtOfHoloOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.EffectiveHS
open ReciprocityTheory.AnForm.M
noncomputable section
open GroundTheory.Heights₂.Heights.EffectiveHS.EffectiveHilbertSamuelJetLemmas
variable {D : ℕ} {U : Type} [TopologicalSpace U]

theorem P2M_GroundTheory_Heights__Heights_EffectiveHS_EffectiveHilbertSamuelJetLemmas_chart_sum_eq_8fb30277a532 (A : FinHolAtlas D U) (s : Fin D → Fin A.n → U → ℂ) (a : ℕ)
    (h : (Fin D → ℕ) → Fin A.n → U → ℂ) (c : Fin A.n) :
    (∑ α ∈ Finset.Nat.antidiagonalTuple D a, sPow s α * h α) c ∘ (A.chart c).symm =
      fun z => ∑ α ∈ Finset.Nat.antidiagonalTuple D a,
        (∏ i, (s i c ∘ (A.chart c).symm) z ^ α i) * (h α c ∘ (A.chart c).symm) z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«EffectiveHS».«EffectiveHilbertSamuelJetLemmas».«chart_sum_eq» := P2M_GroundTheory_Heights__Heights_EffectiveHS_EffectiveHilbertSamuelJetLemmas_chart_sum_eq_8fb30277a532
