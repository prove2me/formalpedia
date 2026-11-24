-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_multinomial_const_2190c1ab2280
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_multinomial_const_2190c1ab2280
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:21.558525+00:00
-- url     : https://prove2.me/theorems/1d2ea2b6-dcf3-433d-8225-b544826c06be
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top multinomial const 2190c1ab2280: P2 M Ground Theory Heights  Heights Rest Terms Top multinomial const 2190c1ab2280
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top multinomial const 2190c1ab2280 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top multinomial const 2190c1ab2280 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSameFactorFormula.lean#L74-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSameFactorFormula.lean#L74-L82

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_multinomial_const_2190c1ab2280 (f x : ℕ) :
    (Nat.multinomial Finset.univ (fun _ : Fin f => x) : ℚ) =
      ((f * x).factorial : ℚ) / (x.factorial : ℚ) ^ f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«multinomial_const» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_multinomial_const_2190c1ab2280
