-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_SolvedInTime_endStatement
-- name    : ThreeSumApsp.WordRam.SolvedInTime.endStatement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-06T08:22:04.146905+00:00
-- url     : https://prove2.me/theorems/fd072547-cb28-47d0-9cfd-f82cce89f6ef
-- title:
--   Convert a real-exponent word-RAM bound to the source specification
-- statement:
--   Let $Q$ be any problem in the shared word-RAM specification, let $a\in\mathbb R$, and let $r\in\mathbb Q$ satisfy $r\ge0$ and $(r:\mathbb R)=a$. Suppose that, for every polynomial input-magnitude exponent $\kappa$, a finite deterministic word-RAM program solves $Q$ on all inputs bounded by $n^\kappa$, at every sufficiently large logarithmic word width, with a step bound $C(n^a+1)$ as specified by `SolvedInTime Q a 0`. Then $Q$ satisfies the source specification's rational-exponent bound: there are a natural-valued step function $T$ and a natural constant $K$ with $T(n)^q\le K n^p$ for all $n\ge2$, where $r=p/q$, and the same program remains correct within $T(n)$ steps on every admissible instance, including the small sizes.
--
--   This shared conversion links Anthropic's running-time theorems to the exact statement format used by both the 3SUM and APSP missions.
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Statements/Exponents.lean#L67-L79

import Definitions.Def_APSPSource_PaperStatements

set_option autoImplicit false
set_option relaxedAutoImplicit false

open ThreeSumApsp.WordRam

theorem ThreeSumApsp.WordRam.SolvedInTime.endStatement {Q : EndStatement.Problem} {a : ℝ} (h : SolvedInTime Q a 0)
    {r : ℚ} (hr : (r : ℝ) = a) (hr0 : 0 ≤ r) : Q.SolvedInTime r := by sorry
