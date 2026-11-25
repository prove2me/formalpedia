-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_monic_shift_coeff_68841b6d0120
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_monic_shift_coeff_68841b6d0120
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:21:18.164689+00:00
-- url     : https://prove2.me/theorems/87c8ddad-6013-45ac-ae65-866dc8bff45e
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists monic shift coeff 68841b6d0120: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets e
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists monic shift coeff 68841b6d0120 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists monic shift coeff 68841b6d0120 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/CoeffEqZeroOfForallEvalEqZero.lean#L33-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/CoeffEqZeroOfForallEvalEqZero.lean#L33-L47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeierstrassPolynomialDivision
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CoeffEqZeroOfForallEvalEqZero
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
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_monic_shift_coeff_68841b6d0120 (N : ℕ) (a : ℂ) :
    ∃ (K₀ : Fin N → ℂ) (K : Fin N → Fin N → ℂ), ∀ (c : Fin N → ℂ) (t : ℂ),
      (t + a) ^ N + ∑ j : Fin N, c j * (t + a) ^ (j : ℕ) =
        t ^ N + ∑ i : Fin N, (K₀ i + ∑ j : Fin N, c j * K i j) * t ^ (i : ℕ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«exists_monic_shift_coeff» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_monic_shift_coeff_68841b6d0120
