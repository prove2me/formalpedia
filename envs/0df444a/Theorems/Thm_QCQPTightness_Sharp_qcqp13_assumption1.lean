-- Prove2me | Theorems.Thm_QCQPTightness_Sharp_qcqp13_assumption1
-- name    : QCQPTightness.Sharp.qcqp13_assumption1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:24:13.103067+00:00
-- url     : https://prove2.me/theorems/d26cd19c-6b2e-469e-b8a5-2be7fd7c4b3f
-- title:
--   §4.3, proof of Proposition 2, p. 22 — Assumption 1 holds for the QCQP (13)
-- statement:
--   For all positive integers $n$ and all $k$, the QCQP (13) satisfies Assumption 1: it is feasible ($x=0$ is feasible) and there is $\gamma$ with $\gamma_1\ge0$ and $A(\gamma)\succ0$ (since $A_1=I\succ0$).
--
--   This is the first bullet of Proposition 2 for the construction (13).
--
--   **Formalization Note** The statement does not need $k\ge1$ and holds for every $k$.
-- source:
--   arXiv:1911.09195v3, §4.3, proof of Proposition 2, p. 22

import Mathlib
import Definitions.Def_QCQPTightness_Sharp_QCQP
import Definitions.Def_QCQPTightness_Sharp_Mult
import Definitions.Def_QCQPTightness_Sharp_Examples

namespace QCQPTightness.Sharp

/-- §4.3, proof of Proposition 2, p. 22: Assumption 1 holds for the QCQP (13). -/
theorem qcqp13_assumption1 (n k : ℕ) (hn : 0 < n) : (qcqp13 n k hn).Assumption1 := by sorry

end QCQPTightness.Sharp
