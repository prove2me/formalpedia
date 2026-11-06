-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_avoidsOutside_iff_neighborhood_subset
-- name    : QEC.Coding.FiberBundle.RandomBase.avoidsOutside_iff_neighborhood_subset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:46:14.593814+00:00
-- url     : https://prove2.me/theorems/a83a9cb6-7292-418c-b0da-71274bb48d36
-- title:
--   Random Base: avoids Outside iff neighborhood subset
-- statement:
--   Avoiding all outside incidences is exactly neighborhood containment.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L395-L427
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L395-L427

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators

theorem QEC.Coding.FiberBundle.RandomBase.avoidsOutside_iff_neighborhood_subset
    {r : Nat} (sample : Sample r)
    (S : Finset (Fin (3 * r)))
    (T : Finset (Fin (4 * r))) :
    AvoidsOutside S T sample ↔
      checkSetNeighborhood sample S ⊆ T := by sorry
