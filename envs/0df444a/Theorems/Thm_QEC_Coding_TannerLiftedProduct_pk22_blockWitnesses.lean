-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_pk22_blockWitnesses
-- name    : QEC.Coding.TannerLiftedProduct.pk22_blockWitnesses
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:29:11.855741+00:00
-- url     : https://prove2.me/theorems/6bd86111-7690-4838-b6dc-17d19d2e731f
-- title:
--   Tanner Lifted Product: pk22 block Witnesses
-- statement:
--   The Tanner Lifted Product construction uses the pk22 block Witnesses property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalParameterSelection.lean#L232-L258
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalParameterSelection.lean#L232-L258

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalParameterSelection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.pk22_blockWitnesses
    (q t : Nat) (hq : 2 ≤ q)
    (hRows : 2 * 124421 ≤ q ^ t)
    (hDistance : 23 ≤ q ^ t) :
    let A := pk22LocalWidth q t
    let D := pk22DistanceCoefficient q t
    let B := pk22RowCoefficient q t
    let L := quadraticWeightBase q A
    D ≤ A ∧ B ≤ A ∧ 0 < L ∧
    (6 * (q + L) ^ A < q ^ B * L ^ (A - D)) ∧
    (6 * (q + L) ^ A < q ^ (A - B) * L ^ (A - D)) ∧
    (6 * (q + L) ^ A < q ^ B * L ^ (A - D)) ∧
    (6 * (q + L) ^ A < q ^ (A - B) * L ^ (A - D)) := by sorry
