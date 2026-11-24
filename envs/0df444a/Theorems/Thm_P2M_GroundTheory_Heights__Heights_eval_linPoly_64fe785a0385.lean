-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval_linPoly_64fe785a0385
-- name    : P2M_GroundTheory_Heights__Heights_eval_linPoly_64fe785a0385
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:58.661749+00:00
-- url     : https://prove2.me/theorems/34bd81e4-4845-49c6-b7dc-db921f5d8fc3
-- title:
--   P2 M Ground Theory Heights  Heights eval lin Poly 64fe785a0385: P2 M Ground Theory Heights  Heights eval lin Poly 64fe785a0385
-- statement:
--   The P2 M Ground Theory Heights  Heights eval lin Poly 64fe785a0385 construction uses the P2 M Ground Theory Heights  Heights eval lin Poly 64fe785a0385 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceObjects.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceObjects.lean#L20-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceObjects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Matrix ComplexSets
noncomputable section
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_eval_linPoly_64fe785a0385 (L : Matrix (Fin d) (Fin n) ℂ) (i : Fin d) (x : Fin n → ℂ) :
    eval x (linPoly L i) = (L *ᵥ x) i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«eval_linPoly» := P2M_GroundTheory_Heights__Heights_eval_linPoly_64fe785a0385
