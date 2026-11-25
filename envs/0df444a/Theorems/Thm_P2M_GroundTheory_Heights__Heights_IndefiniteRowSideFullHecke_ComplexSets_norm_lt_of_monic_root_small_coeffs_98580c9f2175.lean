-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_norm_lt_of_monic_root_small_coeffs_98580c9f2175
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_norm_lt_of_monic_root_small_coeffs_98580c9f2175
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:36:48.82793+00:00
-- url     : https://prove2.me/theorems/5451db4a-8f98-4dca-8f9e-3ee9f534d7ca
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets norm lt of monic root small coeffs 98580c9f2175: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Comp
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets norm lt of monic root small coeffs 98580c9f2175 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets norm lt of monic root small coeffs 98580c9f2175 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/WeierstrassRemainderUnique.lean#L60-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/WeierstrassRemainderUnique.lean#L60-L84

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermWeierstrassPreparation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_WeierstrassRemainderUnique
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
open Topology Filter Polynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_norm_lt_of_monic_root_small_coeffs_98580c9f2175 {d : ℕ} (b : Fin d → ℂ) {r η : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hη : (d : ℝ) * η < r ^ d) (hb : ∀ j, ‖b j‖ ≤ η) (t : ℂ)
    (ht : t ^ d + ∑ j : Fin d, b j * t ^ (j : ℕ) = 0) : ‖t‖ < r := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«norm_lt_of_monic_root_small_coeffs» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_norm_lt_of_monic_root_small_coeffs_98580c9f2175
