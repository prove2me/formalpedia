-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityConjugationCorrectionSum_eq_sum_terms
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityConjugationCorrectionSum_eq_sum_terms
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:03:25.95872+00:00
-- url     : https://prove2.me/theorems/0d951471-a390-4199-b714-0f5dfff5d5c0
-- title:
--   Cartwright Steger: infinity Conjugation Correction Sum eq sum terms
-- statement:
--   The Cartwright Steger construction uses the infinity Conjugation Correction Sum eq sum terms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L937-L942
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L937-L942

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityConjugationCorrectionSum_eq_sum_terms
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k bound : ℕ) (ζ : ConstantExtension P r) :
    infinityConjugationCorrectionSum P r u k bound ζ =
      ∑ i ∈ Finset.range bound, infinityCorrectionTerm P r u k i ζ := by sorry
