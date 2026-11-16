-- Prove2me | Theorems.Thm_SuperRamanujan227_Main_Supplement_theorem_A_1
-- name    : SuperRamanujan227.Main.Supplement.theorem_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:48:37.672209+00:00
-- url     : https://prove2.me/theorems/27bfbc0e-4945-4d80-a715-dccf51ff8b3c
-- title:
--   Theorem A.1 — Quantitative strictness for the entire LPS family
-- statement:
--   Let $p,q$ be distinct primes congruent to $1$ modulo $4$, and let $G=X^{p,q}$ be the LPS arithmetic Cayley multigraph. Its vertex group is $\operatorname{PSL}_2(\mathbb F_q)$ when $p$ is a quadratic residue modulo $q$, and $\operatorname{PGL}_2(\mathbb F_q)$ otherwise. Let $n$ be the actual vertex count and $\lambda(G)$ the largest absolute nontrivial adjacency eigenvalue. Then
--
--   $$\lambda(G)\le2\sqrt p-(4p)^{-(n-1)}.$$
--
--   The degree is $p+1$. This statement covers both residue cases, every admissible pair of primes, and every choice of the square root used in the construction. The subtraction is the exact one established by the norm argument on p.26. No Ramanujan estimate, connectedness, regularity certificate, or Hecke realization is assumed as a hypothesis.
--
--   Differences from the source:
--   - encoding: G=X^{p,q} is an LPS graph on n vertices → the actual arithmetic Cayley adjacency for all admissible primes, any chosen square root of -1, and n equal to its vertex count; reason: the coordinate formula and enumeration specify the named construction; changing the root or enumeration only relabels its spectrum
--   - encoding: the largest absolute nontrivial eigenvalue → maximum after deleting one top eigenvalue and, for a bipartite graph, one bottom eigenvalue, with multiplicity; reason: this removes the canonical trivial directions and retains extra copies in disconnected graphs
-- source:
--   Gil Cohen, Gal Maor, STOC 2027 submission #227 (October 2026), p. 26, Theorem A.1

import Mathlib
import Definitions.Def_SuperRamanujan227_Main_Supplement_LPS

namespace SuperRamanujan227.Main.Supplement

/-- Theorem A.1, p.26: both arithmetic vertex groups, all admissible distinct primes.
The inverse natural power has exponent n-1, never n; no spectral assertion is a hypothesis. -/
theorem theorem_A_1 (p q : ℕ) [Fact q.Prime] (hp : p.Prime)
    (hp4 : p % 4 = 1) (hq4 : q % 4 = 1) (hpq : p ≠ q)
    (i : ZMod q) (hi : i ^ 2 = -1) :
    lpsLambda p q i ≤ 2 * Real.sqrt (p : ℝ) -
      ((4 * (p : ℝ)) ^ (lpsOrder p q - 1))⁻¹ := by sorry

end SuperRamanujan227.Main.Supplement
