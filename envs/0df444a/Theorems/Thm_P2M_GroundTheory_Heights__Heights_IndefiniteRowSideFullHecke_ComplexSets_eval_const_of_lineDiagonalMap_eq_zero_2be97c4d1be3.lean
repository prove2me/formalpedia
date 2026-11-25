-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eval_const_of_lineDiagonalMap_eq_zero_2be97c4d1be3
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eval_const_of_lineDiagonalMap_eq_zero_2be97c4d1be3
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:20:17.153685+00:00
-- url     : https://prove2.me/theorems/5e530725-e1be-4ebd-bfaa-181cad0c854f
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets eval const of line Diagonal Map eq zero 2be97c4d1be3: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets eval const of line Diagonal Map eq zero 2be97c4d1be3 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets eval const of line Diagonal Map eq zero 2be97c4d1be3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNormalModel.lean#L69-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNormalModel.lean#L69-L80

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModel
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
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eval_const_of_lineDiagonalMap_eq_zero_2be97c4d1be3 (c : ℂ) (q : MvPolynomial (Fin 1 ⊕ Fin 1) ℂ)
    (hq : lineDiagonalMap q = 0) : eval (fun _ => c) q = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«eval_const_of_lineDiagonalMap_eq_zero» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eval_const_of_lineDiagonalMap_eq_zero_2be97c4d1be3
