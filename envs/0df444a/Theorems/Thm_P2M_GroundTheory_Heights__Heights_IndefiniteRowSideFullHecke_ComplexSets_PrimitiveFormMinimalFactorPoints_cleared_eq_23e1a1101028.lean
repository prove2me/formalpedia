-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormMinimalFactorPoints_cleared_eq_23e1a1101028
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormMinimalFactorPoints_cleared_eq_23e1a1101028
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:20:53.350972+00:00
-- url     : https://prove2.me/theorems/f011756a-860d-4807-bcef-a999ce50c9a7
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Primitive Form Minimal Factor Points cleared eq 23e1a1101028: P2 M Ground Theory Heights  Heights Indefinite Row Side Fu
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Primitive Form Minimal Factor Points cleared eq 23e1a1101028 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Primitive Form Minimal Factor Points cleared eq 23e1a1101028 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimitiveFormMinimalFactorPoints.lean#L47-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimitiveFormMinimalFactorPoints.lean#L47-L54

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormMinimalFactorPoints_cleared_eq_23e1a1101028 {n : ℕ} (c : Fin n → ℂ) (D x : ℂ) :
    (D * x) ^ n + ∑ j : Fin n, c j * D ^ (n - j) * (D * x) ^ (j : ℕ) =
      D ^ n * (x ^ n + ∑ j : Fin n, c j * x ^ (j : ℕ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«PrimitiveFormMinimalFactorPoints».«cleared_eq» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormMinimalFactorPoints_cleared_eq_23e1a1101028
