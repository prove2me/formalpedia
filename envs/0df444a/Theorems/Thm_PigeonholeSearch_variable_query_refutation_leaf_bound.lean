-- Prove2me | Theorems.Thm_PigeonholeSearch_variable_query_refutation_leaf_bound
-- name    : PigeonholeSearch.variable_query_refutation_leaf_bound
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-27T02:37:49.941093+00:00
-- url     : https://prove2.me/theorems/66dc61f9-9879-54ec-acfc-31bee04db1d9
-- title:
--   An exponential leaf bound for pigeonhole clause search
-- statement:
--   With $n+1$ pigeons and $n$ holes, suppose a binary decision tree queries individual placement variables and, on every Boolean assignment, returns a violated pigeonhole clause. Then the tree has at least $2^n$ leaves. Variables may be queried repeatedly.
-- source:
--   Beyersdorff, Galesi and Lauria, Information Processing Letters 110 (2010), 1074–1077, sections 1, 2 and 4, https://doi.org/10.1016/j.ipl.2010.09.007. The explicit elementary leaf bound here is for the ordinary variable-query search-tree model.

import Definitions.Def_PigeonholeSearch

namespace PigeonholeSearch
theorem variable_query_refutation_leaf_bound (n : ℕ) (t : Tree n)
    (sound : ∀ x : Assignment n, (t.run x).violated x) : 2^n ≤ t.leaves := by sorry
end PigeonholeSearch
