-- Prove2me | Theorems.Thm_TwoOptAllExp_TSP_theorem_1
-- name    : TwoOptAllExp.TSP.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:04:41.398613+00:00
-- url     : https://prove2.me/theorems/8dca14b4-f95b-4709-90ba-c3e7d2c37adb
-- title:
--   Theorem 1 — the TSP with the 2-opt neighborhood has the all-exp property
-- statement:
--   The Traveling Salesman Problem with the 2-opt neighborhood has the all-exp property. That is, there are constants $\varepsilon>0$ and $C>0$ such that for every $m$ there are a TSP instance $I$ of size at least $m$ and a tour $\tau$ of $I$ such that every maximal improving 2-opt sequence from $\tau$ has length at least
--   $$C\cdot2^{\mathrm{size}(I)^{\varepsilon}},$$
--   and at least one such sequence exists.
--
--   The instances are arbitrary complete graphs with natural-number edge weights, the size counts the bits of all edge weights, and the bound holds for every run of 2-opt local search, whatever the pivot rule. Together with the known cases $k\ge3$, it settles the all-exp question for all $k$-opt neighborhoods.
--
--   Differences from the source:
--   - generalization: local search "needs an exponential number of iterations for all possible pivot rules" → also asserts that a maximal improving sequence from the initial tour exists; reason: this excludes a vacuous universal clause; it holds on every finite instance, so the claim of the source is unchanged
--   - encoding: infinitely many pairs of an instance and an initial solution → for every $m$ a pair of size at least $m$; reason: there are finitely many pairs of each size, so the two statements are equivalent; instances differing only on the unused diagonal values of the weight function are not counted as different
--   - encoding: growth $\Omega(2^{n^\epsilon})$ → $C\cdot2^{\mathrm{size}^\varepsilon}\le\ell$ with $\varepsilon,C$ fixed before the instance; reason: finitely many sizes below a threshold can be dropped from an infinite family
--   - encoding: for all pivot rules → every maximal improving sequence; reason: p. 7: the runs of the algorithm are the paths to a sink of the transition graph
--   - encoding: the size of an instance → $N$ plus the bit length plus one of each of the $\binom N2$ weights; reason: the paper fixes no encoding; this one counts every bit of every weight of the complete graph
--   - encoding: weights $c:E\to\mathbb N$ on the complete graph on $V$ → $V=$ `Fin N`, $c$ a function on `Sym2 (Fin N)` whose diagonal values are unused; reason: Lean convention; same instances
--   - encoding: a tour as a Hamiltonian cycle → a tour as the edge set of a Hamiltonian cycle (`IsTourOf`); reason: Lean convention; the swaps of p. 7 act on edge sets
-- source:
--   Heimann, Hoang and Hougardy, Closing All-Exp Gaps in Local Search for the Traveling Salesman Problem and Maximum Constraint Assignment, November 2, 2026 preprint, STOC 2027 submission #112, SHA-256 9ac9fdf5ac1be95dff40e95db1590649f15b4eeb94559413175c88f9a42bff60, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/112.pdf, Theorem 1, p. 3 and p. 13, proof p. 24; Definition 4, p. 7

import Mathlib
import Definitions.Def_TwoOptAllExp_TSP_KOpt

namespace TwoOptAllExp.TSP

/-- **Theorem 1**, p. 3 and p. 13: the Traveling Salesman Problem with the 2-opt neighborhood has the
all-exp property. -/
theorem theorem_1 : HasAllExpProperty (tspKOpt 2) := by sorry

end TwoOptAllExp.TSP
