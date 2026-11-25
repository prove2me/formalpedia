-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eq_zero_on_chart_of_eventually_eq_zero_fd49f49455cd
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eq_zero_on_chart_of_eventually_eq_zero_fd49f49455cd
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:21:04.543954+00:00
-- url     : https://prove2.me/theorems/93a70086-9be9-4b1d-8bd7-bafe7f38095c
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets eq zero on chart of eventually eq zero fd49f49455cd: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets eq zero on chart of eventually eq zero fd49f49455cd construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets eq zero on chart of eventually eq zero fd49f49455cd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegularLocusIdentity.lean#L45-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegularLocusIdentity.lean#L45-L61

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularLocusIdentity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularOffHypersurface
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegularLocusIdentity
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
open MvPolynomial Topology Filter

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eq_zero_on_chart_of_eventually_eq_zero_fd49f49455cd {σ : Type} [Fintype σ] {Y V : Set (σ → ℂ)} {d : ℕ}
    {B : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → σ → ℂ} (hBo : IsOpen B) (hBc : IsPreconnected B)
    (hg : AnalyticOnNhd ℂ g B) (hYV : Y ∩ V = g '' B) (F : (σ → ℂ) → ℂ) (hF : AnalyticOnNhd ℂ F V)
    (h0 : ∃ y ∈ Y ∩ V, ∀ᶠ u in 𝓝 y, u ∈ Y → F u = 0) : ∀ u ∈ Y ∩ V, F u = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«eq_zero_on_chart_of_eventually_eq_zero» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eq_zero_on_chart_of_eventually_eq_zero_fd49f49455cd
