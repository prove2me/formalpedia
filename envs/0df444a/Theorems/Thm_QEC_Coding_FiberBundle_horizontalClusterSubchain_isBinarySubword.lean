-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_horizontalClusterSubchain_isBinarySubword
-- name    : QEC.Coding.FiberBundle.horizontalClusterSubchain_isBinarySubword
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:45:40.299285+00:00
-- url     : https://prove2.me/theorems/fa1069be-75cb-490a-9be2-5d01d4702217
-- title:
--   Fiber Bundle: horizontal Cluster Subchain is Binary Subword
-- statement:
--   A cluster subchain is coordinatewise a subword of the horizontal sector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1474-L1494
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1474-L1494

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.horizontalClusterSubchain_isBinarySubword
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (root : Fin (4 * r) × ZMod (ell * ell)) :
    IsBinarySubword
      (horizontalClusterSubchain
        baseSample twistSample z root)
      (horizontalComponent z) := by sorry
