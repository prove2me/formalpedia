-- Prove2me | Theorems.Thm_Syracuse_first_passage_of_large_valuation_sum
-- name    : Syracuse.first_passage_of_large_valuation_sum
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:46:32.154346+00:00
-- url     : https://prove2.me/theorems/fe8e187f-f907-4ad7-8bc9-9cd7b1913d79
-- title:
--   A finite valuation certificate for Syracuse descent below a threshold
-- statement:
--   Let $x_0=n$ and let $x_{i+1}$ be the odd part of $3x_i+1$. Write $A_k=\sum_{i<k}v_2(3x_i+1)$. For natural numbers $b,n,k$, if $(3b+1)^k n < b^{k+1}2^{A_k}$, then some $x_j$ with $0\le j\le k$ is below $b$.
--
--   The inequality can be checked from a finite prefix and gives a deterministic certificate for crossing the chosen threshold.
-- source:
--   Local derivation: SyracuseValuationBound.lean, syracuse_first_passage_of_large_valuation_sum. The platform map is Definitions.Def_syracuseStep. Original declaration starts at line 41. For the underlying odd-part map on odd inputs, see T. Tao, Almost all orbits of the Collatz map attain almost bounded values, p. 4 before Theorem 1.6, https://arxiv.org/abs/1909.03562. The threshold inequality is the local finite-prefix corollary.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

theorem Syracuse.first_passage_of_large_valuation_sum (b n k : ℕ)
    (h : (3*b+1)^k * n <
      b^k * 2^((Finset.range k).sum fun i => (3*syracuseStep^[i] n+1).factorization 2) * b) :
    ∃ j ≤ k, syracuseStep^[j] n < b := by sorry
