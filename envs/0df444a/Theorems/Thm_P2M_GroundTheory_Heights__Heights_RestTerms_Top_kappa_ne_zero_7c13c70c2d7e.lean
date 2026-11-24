-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_kappa_ne_zero_7c13c70c2d7e
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_kappa_ne_zero_7c13c70c2d7e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:51.706619+00:00
-- url     : https://prove2.me/theorems/1cd2452d-e229-483e-9643-7b66a42de479
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top kappa ne zero 7c13c70c2d7e: P2 M Ground Theory Heights  Heights Rest Terms Top kappa ne zero 7c13c70c2d7e
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top kappa ne zero 7c13c70c2d7e construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top kappa ne zero 7c13c70c2d7e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSameFactorFormula.lean#L93-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSameFactorFormula.lean#L93-L98

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_BlockValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSameFactorFormula
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
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_kappa_ne_zero_7c13c70c2d7e {r a : ℕ} {κ : ℚ}
    (h : κ = (r.factorial : ℚ) * a.factorial ∨ κ = -((r.factorial : ℚ) * a.factorial)) : κ ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«kappa_ne_zero» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_kappa_ne_zero_7c13c70c2d7e
