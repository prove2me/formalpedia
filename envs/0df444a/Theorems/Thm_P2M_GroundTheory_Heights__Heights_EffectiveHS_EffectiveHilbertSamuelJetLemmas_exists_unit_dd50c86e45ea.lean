-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_EffectiveHilbertSamuelJetLemmas_exists_unit_dd50c86e45ea
-- name    : P2M_GroundTheory_Heights__Heights_EffectiveHS_EffectiveHilbertSamuelJetLemmas_exists_unit_dd50c86e45ea
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:55:04.071801+00:00
-- url     : https://prove2.me/theorems/5eb48498-235c-42e8-ac1e-99f78bcad361
-- title:
--   P2 M Ground Theory Heights  Heights Effective HS Effective Hilbert Samuel Jet Lemmas exists unit dd50c86e45ea: P2 M Ground Theory Heights  Heights Effective HS Effective Hilbert Samuel Jet Lemmas exis
-- statement:
--   The P2 M Ground Theory Heights  Heights Effective HS Effective Hilbert Samuel Jet Lemmas exists unit dd50c86e45ea construction uses the P2 M Ground Theory Heights  Heights Effective HS Effective Hilbert Samuel Jet Lemmas exists unit dd50c86e45ea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/AnalyticAtOfHoloOn.lean#L31-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/AnalyticAtOfHoloOn.lean#L31-L53

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

theorem P2M_GroundTheory_Heights__Heights_EffectiveHS_EffectiveHilbertSamuelJetLemmas_exists_unit_dd50c86e45ea {N : ℕ} (A : FinHolAtlas D U) (e : Fin N → Fin A.n → U → ℂ)
    (he : NoCommonZero A e) {S : Set U} (hS : S.Finite) :
    ∃ c : Fin N → ℂ, ∀ x ∈ S, lin e c (chartIdx A x) x ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«EffectiveHS».«EffectiveHilbertSamuelJetLemmas».«exists_unit» := P2M_GroundTheory_Heights__Heights_EffectiveHS_EffectiveHilbertSamuelJetLemmas_exists_unit_dd50c86e45ea
