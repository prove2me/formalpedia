-- Prove2me | Theorems.Thm_TreeOrient_RecGreedy_Supplement_proposition_2_4
-- name    : TreeOrient.RecGreedy.Supplement.proposition_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T00:52:55.891801+00:00
-- url     : https://prove2.me/theorems/5a62f2ba-b3e5-410c-8427-42a2432a1e0a
-- title:
--   Proposition 2.4 (corrected: B + 1 budget guesses) — Algorithm 1 at depth i takes O((n(B+1)·2^{d+2})^i) steps
-- statement:
--   Consider Algorithm 1, the recursive greedy procedure $RG(r,Y,B,X,i)$, on an instance with $n$ vertices and integer edge costs, and let $d$ be the depth of the top-level call $RG(r^*,\emptyset,B,\emptyset,d)$. By Proposition 2.3 every subproblem $RG(r,Y,B,X,i)$ of that call satisfies $|Y|+i\le d$. There is an absolute constant $c>0$ such that every call with $i\ge1$ and $|Y|+i\le d$ takes at most
--
--   $$c\,\bigl(n\,(B+1)\,2^{d+2}\bigr)^{i}$$
--
--   steps. The constant does not depend on the instance, on $r$, $Y$, $B$, $X$, $i$ or $d$.
--
--   This is the running-time half of Theorem 2.6: with $d=\lceil\log_{3/2}k\rceil$ and $Y=\emptyset$ it gives a bound of the form $(nB)^{O(\log k)}$.
--
--   **Formalization Note** The call is the published `rg I 1 .enum`, and the step count is the published model's: $1$ per call, $n$ per base call, plus every recursive call and $1$ per evaluated candidate. The algorithm guesses the budget split $B_1$ in $[0,B]$, that is $B+1$ values, hence $B+1$ in place of $B$.
--
--   Differences from the source:
--   - correction: running time $O((nB\cdot2^{d+2})^i)$ → at most $c\,(n(B+1)2^{d+2})^i$ steps; reason: the published algorithm guesses $B_1\in[0,B]$ ($B+1$ values; zero-cost edges need $B_1=0$), and the printed bound is $0$ at $B=0$ although every call takes at least one step.
--   - reading: a call $RG(r,Y,B,X,i)$ inside the top call $RG(r^*,\emptyset,B,\emptyset,d)$ → every call with $|Y|+i\le d$; reason: this is Proposition 2.3's invariant, which the proof uses as $|Y|\le d$ to count $2^d$ responsibility guesses; it holds for every subproblem of the top call.
--   - encoding: running time → step count of the published model; reason: the model's count charges every call, base-case scan, sub-call and candidate evaluation, so it is never less than the operations the proof counts.
-- source:
--   Ghuge & Nagarajan, arXiv:1812.01768v2, pp. 5–6 (PDF 6–7), Proposition 2.4 and its proof; Proposition 2.3, p. 5 (PDF 6)

import Mathlib
import Definitions.Def_TreeOrient_RecGreedy_Model

namespace TreeOrient.RecGreedy.Supplement

/-- Proposition 2.4, p. 5 (PDF 6): the step count of Algorithm 1 at depth `i` inside the
top call of depth `d`, under Proposition 2.3's invariant `|Y| + i ≤ d`. -/
theorem proposition_2_4 : ∃ c : ℝ, 0 < c ∧
    ∀ (n : ℕ) (I : Inst n) (r : Fin n) (Y : Finset (Fin n)) (B : ℕ) (X : Finset (Fin n))
      (i d : ℕ), 1 ≤ i → Y.card + i ≤ d →
      ((rg I 1 .enum i r Y B X).2 : ℝ) ≤
        c * ((n : ℝ) * ((B : ℝ) + 1) * 2 ^ (d + 2)) ^ i := by sorry

end TreeOrient.RecGreedy.Supplement
