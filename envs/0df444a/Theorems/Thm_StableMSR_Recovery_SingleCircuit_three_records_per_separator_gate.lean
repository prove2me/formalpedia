-- Prove2me | Theorems.Thm_StableMSR_Recovery_SingleCircuit_three_records_per_separator_gate
-- name    : StableMSR.Recovery.SingleCircuit.three_records_per_separator_gate
-- status  : Open
-- author  : @lreyzin
-- created : 2026-11-23T00:04:33.920795+00:00
-- url     : https://prove2.me/theorems/37b9a10f-8c8e-4b5a-be52-b67ae6265604
-- title:
--   Three native records per gate preserve the entire ordered witness language
-- statement:
--   A physical record trace at any state is equivalent to an abstract circuit derivation of the same ordered block list. An OR gate has two left ports and a shared empty right port. An AND gate has one port on each side. The proof covers unreachable, out-of-range, and forward-pointing operands.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, https://arxiv.org/abs/2611.03547. This contribution specializes the mission’s tight-block recurrence to singleton progress for the native separator construction.

import Definitions.Def_StableMSR_SingleSeparatorCircuit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 15000
open StableMSR.Recovery StableMSR.Recovery.WindowPorts StableMSR.Recovery.WindowMasks StableMSR.Recovery.SingleCircuit

theorem StableMSR.Recovery.SingleCircuit.three_records_per_separator_gate (n : ℕ) (g : Gates) (roots : ℕ→ℕ) (live : 0< g.size) (zero : gateAt g 0=.atom [])
    (p : ℕ) (L : List (Cluster n)) :
    WindowMasks.Trace (boardOf g roots) (maskAt n g) p L ↔ Language n g p L := by sorry
