-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormMinimalFactorPoints_eval__eq_zero_of_dvd_aea6d61b0052
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormMinimalFactorPoints_eval__eq_zero_of_dvd_aea6d61b0052
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:20:30.422393+00:00
-- url     : https://prove2.me/theorems/a5b1226e-bcc6-409c-b424-647b1ee435f1
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Primitive Form Minimal Factor Points eval  eq zero of dvd aea6d61b0052: P2 M Ground Theory Heights  Heights Indefinite R
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Primitive Form Minimal Factor Points eval  eq zero of dvd aea6d61b0052 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Primitive Form Minimal Factor Points eval  eq zero of dvd aea6d61b0052 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimitiveFormMinimalFactorPoints.lean#L38-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimitiveFormMinimalFactorPoints.lean#L38-L45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormMinimalFactorPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermMinimalPolynomialDivides
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteFibreCentredEquation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormRemainder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveFormMinimalFactorPoints
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
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PrimitiveFormMinimalFactorPoints
open Topology Filter Polynomial

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormMinimalFactorPoints_eval__eq_zero_of_dvd_aea6d61b0052 {d n : ℕ} {b : Fin n → (Fin d → ℂ) → ℂ} {y : Fin d → ℂ}
    {E : Polynomial ((Fin d → ℂ) → ℂ)}
    (hd : (X ^ n + ∑ j, C (b j y) * X ^ (j : ℕ) : Polynomial ℂ) ∣ E.map (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) y))
    {τ : ℂ} (hτ : τ ^ n + ∑ j, b j y * τ ^ (j : ℕ) = 0) :
    E.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) y) τ = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«PrimitiveFormMinimalFactorPoints».«eval₂_eq_zero_of_dvd» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormMinimalFactorPoints_eval__eq_zero_of_dvd_aea6d61b0052
