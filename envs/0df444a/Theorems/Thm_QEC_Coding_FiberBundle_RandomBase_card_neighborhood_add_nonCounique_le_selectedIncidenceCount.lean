-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_card_neighborhood_add_nonCounique_le_selectedIncidenceCount
-- name    : QEC.Coding.FiberBundle.RandomBase.card_neighborhood_add_nonCounique_le_selectedIncidenceCount
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:45:32.990853+00:00
-- url     : https://prove2.me/theorems/750fcdd6-bd7e-4618-a772-b4bbee5600b4
-- title:
--   Random Base: card neighborhood add non Counique le selected Incidence Count
-- statement:
--   The selected incidence count is at least one token per neighbor plus one
--   additional token per non-counique neighbor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L180-L213
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L180-L213

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators

theorem QEC.Coding.FiberBundle.RandomBase.card_neighborhood_add_nonCounique_le_selectedIncidenceCount
    {r : Nat} (sample : Sample r)
    (S : Finset (Fin (3 * r))) :
    (checkSetNeighborhood sample S).card +
        (nonCouniqueNeighbors sample S).card ≤
      selectedIncidenceCount sample S := by sorry
