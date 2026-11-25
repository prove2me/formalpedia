-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_goodPosition_line_6107b469ad64
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_goodPosition_line_6107b469ad64
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:20:33.843217+00:00
-- url     : https://prove2.me/theorems/a1d6e2c4-e2e4-5c7f-8fc6-ee4a0a769bc9
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets good Position line 6107b469ad64: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets good Po
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets good Position line 6107b469ad64 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets good Position line 6107b469ad64 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/EqZeroOfMemZeroLocusLineOriginIdeal.lean#L310-L346
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/EqZeroOfMemZeroLocusLineOriginIdeal.lean#L310-L346

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal
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
open MvPolynomial MeasureTheory Filter Topology Matrix
open scoped ContDiff ENNReal
noncomputable section
variable {n d e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_goodPosition_line_6107b469ad64 :
    GoodPosition (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) lineOriginIdeal (fun _ => 1) 0
      (0 : Matrix (Fin 0) (Fin 1) ℂ) (Metric.ball 0 1) Set.univ 1 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«goodPosition_line» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_goodPosition_line_6107b469ad64
