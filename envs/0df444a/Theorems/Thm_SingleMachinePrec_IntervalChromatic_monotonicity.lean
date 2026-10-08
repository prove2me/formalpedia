-- Prove2me | Theorems.Thm_SingleMachinePrec_IntervalChromatic_monotonicity
-- name    : SingleMachinePrec.IntervalChromatic.monotonicity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:27:01.065129+00:00
-- url     : https://prove2.me/theorems/f1abdd7a-4fc6-4722-acc2-ba44c0275fb6
-- title:
--   §4.2 — chromatic number is nondecreasing
-- statement:
--   For $n\ge2$, the graph of ordered incomparable pairs of the canonical interval order $I_n$ cannot require more colors than the corresponding graph for $I_{n+1}$. Equivalently, for every $k\ge0$,
--
--   $$
--   G_{I_{n+1}}\text{ is $k$-colorable}\quad\Longrightarrow\quad G_{I_n}\text{ is $k$-colorable}.
--   $$
--
--   This is the monotonicity assertion used immediately before Theorem 4.3.
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 658, §4.2, first sentence of proof of Theorem 4.3; DOI 10.1287/moor.1110.0512

import Definitions.Def_SingleMachinePrec_IntervalChromatic_CanonicalOrder

namespace SingleMachinePrec.IntervalChromatic

/-- Section 4.2, p. 658: the chromatic number of `G (I n)` is nondecreasing. -/
theorem monotonicity (n k : ℕ) (hn : 2 ≤ n) :
    Colorable (n + 1) k → Colorable n k := by sorry

end SingleMachinePrec.IntervalChromatic
