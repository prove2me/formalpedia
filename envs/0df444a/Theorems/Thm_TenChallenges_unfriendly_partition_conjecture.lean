-- Prove2me | Theorems.Thm_TenChallenges_unfriendly_partition_conjecture
-- name    : TenChallenges.unfriendly_partition_conjecture
-- status  : Open
-- author  : @utkuokur
-- created : 2026-11-04T20:45:06.430201+00:00
-- url     : https://prove2.me/theorems/bc6dbb59-13db-4b08-b20f-07609d387aa1
-- title:
--   Unfriendly partition conjecture: every countable graph has an unfriendly partition
-- statement:
--   **The unfriendly partition conjecture** (Cowan and Emerson). Every graph $G$ on a countable vertex set has an **unfriendly partition**: a map $f\colon V(G)\to\{0,1\}$ such that every vertex $v$ has at least as many neighbours in the class opposite to $f(v)$ as in its own class,
--
--   $$\forall v:\quad \big|N(v)\cap f^{-1}[1-f(v)]\big|\ \ge\ \big|N(v)\cap f^{-1}[f(v)]\big| ,$$
--
--   the comparison being one of cardinal numbers. Finite graphs, locally finite graphs, graphs with finitely many vertices of infinite degree and rayless graphs are known to have unfriendly partitions; uncountable graphs need not; the countable case is open.
--
--   **Formalization Note.** The partition is a function `V → Option Bool` that is unfriendly at every vertex in the sense of `UnfriendlyAt`; since unfriendliness at $v$ requires $f(v)$ to be defined, such a function is total. The vertex type is `Countable` and lives in an arbitrary universe.
-- source:
--   Unfriendly partition conjecture (Cowan and Emerson), as stated in R. Aharoni, E. C. Milner, K. Prikry, Unfriendly partitions of a graph, JCTB 50 (1990), 1–10, https://doi.org/10.1016/0095-8956(90)90092-E, introduction (the countable case); unfriendliness as in the Ten Challenges repository, Defs_and_Lems/UnfriendlyPartition.lean

import Definitions.Def_TenChallenges_Challenge_10
universe u

namespace TenChallenges
theorem unfriendly_partition_conjecture {V : Type u} [Countable V] (G : SimpleGraph V) :
    ∃ f : V → Option Bool, ∀ v, UnfriendlyAt G f v := by sorry
end TenChallenges
