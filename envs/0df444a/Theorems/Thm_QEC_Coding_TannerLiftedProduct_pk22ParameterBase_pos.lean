-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_pk22ParameterBase_pos
-- name    : QEC.Coding.TannerLiftedProduct.pk22ParameterBase_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:14:58.365077+00:00
-- url     : https://prove2.me/theorems/0baab41d-383c-419d-a3b3-2e7171f765d9
-- title:
--   Tanner Lifted Product: pk22 Parameter Base pos
-- statement:
--   The Tanner Lifted Product construction uses the pk22 Parameter Base pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalParameterSelection.lean#L37-L39
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalParameterSelection.lean#L37-L39

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalParameterSelection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.pk22ParameterBase_pos (q t : Nat) :
    0 < pk22ParameterBase q t := by sorry
