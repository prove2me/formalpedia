-- Prove2me | Theorems.Thm_StrategyProofArrow_Correspondence_cs_of_po
-- name    : StrategyProofArrow.Correspondence.cs_of_po
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:48:35.442452+00:00
-- url     : https://prove2.me/theorems/10e835b6-b2c4-416e-8405-ff22d5a99e60
-- title:
--   §4, p. 31 — Pareto optimality implies citizens' sovereignty
-- statement:
--   Let $n\ge2$, $m\ge3$, and let $u:\rho_m^n\to\rho_m$ be a strict social welfare function on the committee $I_n$ and the alternative set $S_m$. If $u$ satisfies Pareto optimality (PO), then it satisfies citizens' sovereignty (CS): for all distinct $x,y\in S_m$ there is a strict ballot set $B$ with
--   $$x\,\bar A\,y,\qquad A=u(B).$$
--
--   The paper uses this observation to conclude that the social welfare function Gibbard builds from a strategy-proof voting procedure, which is Pareto optimal, also satisfies CS.
--
--   **Formalization Note** The paper's observation carries no cardinality conditions; the standing hypotheses $n\ge2$, $m\ge3$ of §4 are kept. CS is read for $x\ne y$. Definitions as in `StrategyProofArrow.Correspondence.Basic`.
-- source:
--   Satterthwaite, Strategy-proofness and Arrow's Conditions, Northwestern Discussion Paper No. 122 (rev. Dec. 12, 1974), §4, p. 31 ("Observe that if a social welfare function satisfies PO, then it also satisfies CS"), used p. 33

import Mathlib
import Definitions.Def_StrategyProofArrow_Correspondence_Basic

namespace StrategyProofArrow.Correspondence

theorem cs_of_po {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι] [DecidableEq A]
    (hn : 2 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (u : StrongProfile ι A → StrongOrder A) (hpo : PO u) :
    CS u := by sorry

end StrategyProofArrow.Correspondence
