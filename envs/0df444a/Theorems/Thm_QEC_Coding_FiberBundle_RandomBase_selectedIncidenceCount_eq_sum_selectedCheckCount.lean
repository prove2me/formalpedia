-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_selectedIncidenceCount_eq_sum_selectedCheckCount
-- name    : QEC.Coding.FiberBundle.RandomBase.selectedIncidenceCount_eq_sum_selectedCheckCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:46:51.593691+00:00
-- url     : https://prove2.me/theorems/20bb124c-0f53-4a60-b32c-f201dc3ea6f8
-- title:
--   Random Base: selected Incidence Count eq sum selected Check Count
-- statement:
--   Double-count selected incidences by checks or by variables.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L150-L158
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L150-L158

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators

theorem QEC.Coding.FiberBundle.RandomBase.selectedIncidenceCount_eq_sum_selectedCheckCount
    {r : Nat} (sample : Sample r)
    (S : Finset (Fin (3 * r))) :
    selectedIncidenceCount sample S =
      ∑ b : Fin (4 * r), selectedCheckCount sample S b := by sorry
