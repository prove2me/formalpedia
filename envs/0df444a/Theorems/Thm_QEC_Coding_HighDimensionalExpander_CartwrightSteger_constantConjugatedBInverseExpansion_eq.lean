-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantConjugatedBInverseExpansion_eq
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantConjugatedBInverseExpansion_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:03:15.548005+00:00
-- url     : https://prove2.me/theorems/9282351d-e04d-4938-a9a5-549f309782bc
-- title:
--   Cartwright Steger: constant Conjugated BInverse Expansion eq
-- statement:
--   The Cartwright Steger construction uses the constant Conjugated BInverse Expansion eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L608-L613
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L608-L613

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantConjugatedBInverseExpansion_eq
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    constantConjugatedBInverseExpansion P r u =
      1 + (splittingY P r)⁻¹ •
        constantConjugatedBInverseTail P r u := by sorry
