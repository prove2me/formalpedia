-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_card_hho20_qubitIndex
-- name    : QEC.Coding.FiberBundle.card_hho20_qubitIndex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:54:56.42175+00:00
-- url     : https://prove2.me/theorems/9d3f230d-587e-427c-835f-6c509445682c
-- title:
--   Fiber Bundle: card hho20 qubit Index
-- statement:
--   Exact number of total-degree-one cells in the HHO20 bundle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/InitialCode.lean#L17-L25
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/InitialCode.lean#L17-L25

import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Parameters
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialCode
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle

theorem QEC.Coding.FiberBundle.card_hho20_qubitIndex
    (r ell : Nat) [NeZero ell] :
    Fintype.card
        (QubitIndex (Fin (3 * r)) (Fin (4 * r))
          (ZMod (ell * ell)) (ZMod (ell * ell))) =
      7 * r * (ell * ell) := by sorry
