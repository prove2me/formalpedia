-- Prove2me | Theorems.Thm_QAlgorithms_Papers_LinLin16_firstMarked_search
-- name    : QAlgorithms.Papers.LinLin16.firstMarked_search
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T18:46:16.04619+00:00
-- url     : https://prove2.me/theorems/d4ad5e2d-e31c-4fc8-a6ec-4f73fdbc9e9a
-- title:
--   Finding the first marked element with O(√d) expected queries
-- statement:
--   This is the quantum algorithm for finding the first marked element of an ordered list (Lin–Lin, Theorem 10).
--
--   A list of $N$ elements is given as a black box $x\in\{0,1\}^N$, where $x_i=1$ means that element $i$ is marked; it is accessed through the standard query oracle $O_x:|i,b\rangle\mapsto|i,b\oplus x_i\rangle$. An algorithm consists of rounds; each round applies $U_T O_x U_{T-1}\cdots O_x U_0$ to a fixed start state with unitaries $U_t$ independent of $x$, measures in the computational basis, and chooses the next round (or halts with an answer) from the outcome. For an input $x$ let $\mathrm{first}(x)$ be the position of the first marked element, or $\bot$ if none is marked.
--
--   There is an absolute constant $C>0$ such that for every $N$ there is an algorithm $\mathcal A$, fixed before the input, such that for every $x\in\{0,1\}^N$:
--
--   1. $\Pr[\mathcal A \text{ outputs } \mathrm{first}(x)]\ge 9/10$;
--   2. if the first marked element is the $d$-th element of the list, then the expected number of queries satisfies
--   $$\mathbb E[\#\text{queries of }\mathcal A\text{ on }x]\le C\sqrt d;$$
--   3. if no element is marked, then $\mathcal A$ outputs $\bot$ with probability $1$, and every run uses at most $C\sqrt N$ queries.
--
--   The point is that the cost adapts to the position of the first marked element rather than to the length of the list; this is the search subroutine used to simulate classical query algorithms whose query results can be guessed.
--
--   **Formalization Note** Algorithms are finite trees of query rounds with measurements in between. Positions are 0-indexed, so the $d$-th element is index $d-1$ and the bound reads $C\sqrt{i+1}$. The error constant $1/10$ is the one achieved by the paper's proof (Appendix C). The source's time bounds are not formalized, because the paper fixes no model of time; only the query bounds are stated.
-- source:
--   Upper bounds on quantum query complexity inspired by the Elitzur-Vaidman bomb tester (Lin, Lin), arXiv:1410.0932v2, Theorem 10, PDF p. 13. https://arxiv.org/abs/1410.0932v2 . PDF SHA-256: 380f35f0b5a6e78b01b84d742a6b253496b541eeeac90285a6d683bf774f9c5e.

import Definitions.Def_QAlgorithms_Defs_AdaptiveQuery
set_option autoImplicit false

namespace QAlgorithms.Papers.LinLin16

/-- **Theorem 10** (LinLin p.13; restated and proved in Appendix C, p.31–32): finding the first
marked element in a list. There is an absolute constant `C > 0` such that for every list length
`N` there is a quantum query algorithm (fixed before the input, built from input-independent
unitaries and the XOR oracle) which, for every input `x : Fin N → Bool`,

* outputs the first marked element (`some i`) or "no marked element" (`none`), correctly with
  probability at least `9/10` (bounded error; the proof's total error is `δ < 1/10`);
* if the first marked element is the `d`-th element (index `i = d - 1`), uses an expected number
  of queries at most `C √d`;
* if there are no marked elements, uses at most `C √N` queries on every run and always outputs
  `none`.

The "time" bounds of the source are not formalized (the paper fixes no time model). -/
theorem firstMarked_search :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ A : AdaptiveQueryAlg (Fin N) (Option (Fin N)),
      ∀ x : Fin N → Bool,
        A.outProb x (firstMarked x) ≥ 9 / 10 ∧
        (∀ i : Fin N, firstMarked x = some i →
          A.expQueries x ≤ C * Real.sqrt ((i : ℝ) + 1)) ∧
        (firstMarked x = none →
          A.outProb x none = 1 ∧ (A.maxQueries x : ℝ) ≤ C * Real.sqrt N) := by
  sorry

end QAlgorithms.Papers.LinLin16
