-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_HammingWeight_randomFiberBundle_base_col_eq_variableDegree
-- name    : QEC.Coding.FiberBundle.RandomBase.HammingWeight_randomFiberBundle_base_col_eq_variableDegree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:40:50.071598+00:00
-- url     : https://prove2.me/theorems/de92e295-b9f5-460c-9ad7-e74f7f547bb8
-- title:
--   Random Base: Hamming Weight random Fiber Bundle base col eq variable Degree
-- statement:
--   The Random Base construction uses the Hamming Weight random Fiber Bundle base col eq variable Degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/InitialLocality.lean#L43-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/InitialLocality.lean#L43-L55

import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialCode
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialLocality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
open QEC.Coding
open QEC.Coding.FiberBundle.RandomBase

theorem QEC.Coding.FiberBundle.RandomBase.HammingWeight_randomFiberBundle_base_col_eq_variableDegree
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (b : Fin (4 * r)) :
    HammingWeight
        (fun a => (RandomTwist.fiberBundleData
          baseSample twistSample).baseBoundary a b) =
      variableDegree baseSample b := by sorry
