-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_binary_cycle_toggle_indicator_identity
-- name    : QEC.Coding.FiberBundle.binary_cycle_toggle_indicator_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:53:22.269239+00:00
-- url     : https://prove2.me/theorems/ae01b46d-2f9c-4a96-ada1-da93beb454fb
-- title:
--   Fiber Bundle: binary cycle toggle indicator identity
-- statement:
--   At a genuine boundary vertex of a binary cycle chain, toggling the edge after
--   the vertex and toggling the edge before it have complementary weight changes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L3296-L3326
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L3296-L3326

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.binary_cycle_toggle_indicator_identity
    (a b g : ZMod 2)
    (hg : g ≠ 0 → g = a + b) :
    (if a + g ≠ 0 then 1 else 0) +
        (if b + g ≠ 0 then 1 else 0) =
      (if a ≠ 0 then 1 else 0) +
        (if b ≠ 0 then 1 else 0) := by sorry
