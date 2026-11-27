-- Prove2me | Theorems.Thm_PigeonholeSearch_exists_polynomial_shared_clause_search
-- name    : PigeonholeSearch.exists_polynomial_shared_clause_search
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-27T02:40:52.41609+00:00
-- url     : https://prove2.me/theorems/468fd3ae-8d12-58d1-8a14-160df612a3a7
-- title:
--   Polynomially many shared states suffice for pigeonhole clause search
-- statement:
--   For every number of holes $n$, there exists a variable-query tree that reports a violated clause of the unary pigeonhole formula on every assignment. Its root belongs to a set of states closed under taking both children, whose cardinality is at most $1+(n+3)((n+1)+(n+1)^2n)$. Identical subtrees are counted once in this set. The construction permits repeated variable queries.
-- source:
--   Stasys Jukna, Boolean Function Complexity, section 18.2, Resolution and branching programs, the sequential branching program for clause search. https://web.vu.lt/mif/s.jukna/boolean/bool-V7.pdf . For the pigeonhole clause family see Beyersdorff, Galesi and Lauria, IPL 110 (2010), section 4, https://doi.org/10.1016/j.ipl.2010.09.007 . The displayed finite bound counts the explicit search states in this construction.

import Definitions.Def_PigeonholeSearch

namespace PigeonholeSearch
theorem exists_polynomial_shared_clause_search (n : ℕ) :
    ∃ (t : Tree n) (states : Finset (Tree n)), t ∈ states ∧
      (∀ p h no yes, Tree.query p h no yes ∈ states → no ∈ states ∧ yes ∈ states) ∧
      (∀ x : Assignment n, (t.run x).violated x) ∧
      states.card ≤ 1 + (n+3)*((n+1) + (n+1)*((n+1)*n)) := by sorry
end PigeonholeSearch
