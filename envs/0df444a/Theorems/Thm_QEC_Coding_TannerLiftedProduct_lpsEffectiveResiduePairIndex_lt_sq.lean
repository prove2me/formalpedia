-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveResiduePairIndex_lt_sq
-- name    : QEC.Coding.TannerLiftedProduct.lpsEffectiveResiduePairIndex_lt_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:46:04.690059+00:00
-- url     : https://prove2.me/theorems/dbfec058-ccb3-4eaf-91c5-528cc188cfbd
-- title:
--   Tanner Lifted Product: lps Effective Residue Pair Index lt sq
-- statement:
--   The Tanner Lifted Product construction uses the lps Effective Residue Pair Index lt sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSResidueCoordinates.lean#L54-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSResidueCoordinates.lean#L54-L56

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Find
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSResidueCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.lpsEffectiveResiduePairIndex_lt_sq (q : ℕ) [Fact q.Prime] :
    lpsEffectiveResiduePairIndex q < q ^ 2 := by sorry
