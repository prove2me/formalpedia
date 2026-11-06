-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_selectedIncidenceCount_upper
-- name    : QEC.Coding.FiberBundle.RandomBase.selectedIncidenceCount_upper
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:45:36.594564+00:00
-- url     : https://prove2.me/theorems/15c83190-6c53-4d4e-892a-dec1ad3e6ca1
-- title:
--   Random Base: selected Incidence Count upper
-- statement:
--   The check-degree upper window bounds selected incidences.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L227-L241
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L227-L241

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators

theorem QEC.Coding.FiberBundle.RandomBase.selectedIncidenceCount_upper
    {r Delta : Nat} {sample : Sample r}
    (hDegree : HasDegreeWindows (Delta := Delta) sample)
    (S : Finset (Fin (3 * r))) :
    100 * selectedIncidenceCount sample S ≤
      101 * Delta * S.card := by sorry
