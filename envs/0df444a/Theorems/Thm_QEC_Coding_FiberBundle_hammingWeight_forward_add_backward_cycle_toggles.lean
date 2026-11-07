-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_forward_add_backward_cycle_toggles
-- name    : QEC.Coding.FiberBundle.hammingWeight_forward_add_backward_cycle_toggles
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:53:33.796698+00:00
-- url     : https://prove2.me/theorems/e46dafe1-41db-4cd5-a8f3-55ef05379342
-- title:
--   Fiber Bundle: hamming Weight forward add backward cycle toggles
-- statement:
--   If a selected vertex set is supported inside the actual boundary of a cycle
--   chain, the two possible vertical slides have exactly complementary total
--   weight changes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L3333-L3393
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L3333-L3393

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.hammingWeight_forward_add_backward_cycle_toggles
    (n : Nat) [NeZero n] (hn : 2 ≤ n)
    (v g : Word (ZMod 2) (ZMod n))
    (hgBoundary : ∀ j, g j ≠ 0 →
      g j = cycleFiberChainBoundary n v j) :
    HammingWeight (v + g) +
        HammingWeight (v + backwardVertexToggle n g) =
      2 * HammingWeight v := by sorry
