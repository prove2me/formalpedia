-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_EffectiveHilbertSamuelJetLemmas_analyticAt_of_holoOn_c7b3bffc3f2a
-- name    : P2M_GroundTheory_Heights__Heights_EffectiveHS_EffectiveHilbertSamuelJetLemmas_analyticAt_of_holoOn_c7b3bffc3f2a
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:18:36.008984+00:00
-- url     : https://prove2.me/theorems/b9bb7fdc-909c-4e20-a02e-41e0392d88cf
-- title:
--   P2 M Ground Theory Heights  Heights Effective HS Effective Hilbert Samuel Jet Lemmas analytic At of holo On c7b3bffc3f2a: P2 M Ground Theory Heights  Heights Effective HS Effective Hilbert Samuel Jet
-- statement:
--   The P2 M Ground Theory Heights  Heights Effective HS Effective Hilbert Samuel Jet Lemmas analytic At of holo On c7b3bffc3f2a construction uses the P2 M Ground Theory Heights  Heights Effective HS Effective Hilbert Samuel Jet Lemmas analytic At of holo On c7b3bffc3f2a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/AnalyticAtOfHoloOn.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/AnalyticAtOfHoloOn.lean#L26-L29

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

theorem P2M_GroundTheory_Heights__Heights_EffectiveHS_EffectiveHilbertSamuelJetLemmas_analyticAt_of_holoOn_c7b3bffc3f2a (A : FinHolAtlas D U) {f : U → ℂ} {c : Fin A.n}
    (hf : A.HoloOn (A.chart c).source f) {x : U} (hx : x ∈ (A.chart c).source) :
    AnalyticAt ℂ (f ∘ (A.chart c).symm) (A.chart c x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«EffectiveHS».«EffectiveHilbertSamuelJetLemmas».«analyticAt_of_holoOn» := P2M_GroundTheory_Heights__Heights_EffectiveHS_EffectiveHilbertSamuelJetLemmas_analyticAt_of_holoOn_c7b3bffc3f2a
