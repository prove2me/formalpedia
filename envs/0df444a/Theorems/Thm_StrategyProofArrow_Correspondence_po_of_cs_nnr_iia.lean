-- Prove2me | Theorems.Thm_StrategyProofArrow_Correspondence_po_of_cs_nnr_iia
-- name    : StrategyProofArrow.Correspondence.po_of_cs_nnr_iia
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:50:23.484844+00:00
-- url     : https://prove2.me/theorems/6b46fca5-824a-48c2-9493-d9fa1001e2ef
-- title:
--   §4, p. 31 — CS, NNR and IIA imply Pareto optimality (strict social welfare functions)
-- statement:
--   Let $I_n$ be a committee of $n\ge2$ individuals and $S_m$ a set of $m\ge3$ alternatives, and let $u:\rho_m^n\to\rho_m$ be a strict social welfare function. If $u$ satisfies citizens' sovereignty (CS), non-negative response (NNR) and independence of irrelevant alternatives (IIA), then $u$ is Pareto optimal: for every strict ballot set $B$ and alternatives $x,y$,
--   $$x\,\bar B_i\,y\ \text{ for all } i\in I_n\quad\Longrightarrow\quad x\,\bar A\,y,\qquad A=u(B).$$
--
--   The paper attributes this to Arrow [1, p. 97]. It is the first step of Lemma 7: Pareto optimality is what guarantees that the voting procedure derived from $u$ reaches every alternative.
--
--   **Formalization Note** The paper states the claim without cardinality conditions; we state it under the standing hypotheses $n\ge2$, $m\ge3$ of §4 (Lemma 7, Lemma 8, Theorem 2). Some hypothesis is needed: with $n=0$ and $m=1$ CS, NNR and IIA hold vacuously but PO fails. CS is read for $x\ne y$. Definitions and conventions as in `StrategyProofArrow.Correspondence.Basic`.
-- source:
--   Satterthwaite, Strategy-proofness and Arrow's Conditions, Northwestern Discussion Paper No. 122 (rev. Dec. 12, 1974), §4, p. 31 (citing Arrow, Social Choice and Individual Values, p. 97)

import Mathlib
import Definitions.Def_StrategyProofArrow_Correspondence_Basic

namespace StrategyProofArrow.Correspondence

theorem po_of_cs_nnr_iia {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι] [DecidableEq A]
    (hn : 2 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (u : StrongProfile ι A → StrongOrder A) (hcs : CS u) (hnnr : NNR u) (hiia : IIA u) :
    PO u := by sorry

end StrategyProofArrow.Correspondence
