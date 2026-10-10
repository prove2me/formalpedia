-- Prove2me | Theorems.Thm_PowerOfDUniversality_Fluid_proposition_3_1
-- name    : PowerOfDUniversality.Fluid.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:39:56.244394+00:00
-- url     : https://prove2.me/theorems/9bde62d2-aa9f-43b8-a419-2d39da67a81e
-- title:
--   Proposition 3.1 — one step of Rule(n_A, n_B, k) with n_A ≤ n_B preserves the stack ordering (3.1)
-- statement:
--   Let $A$ and $B$ be two ensembles of $N\ge 1$ stacks with maximum height $b\ge 1$: occupancy vectors $\mathbf Q^A,\mathbf Q^B$ of $N$ servers with buffer $b$ (with $Q_0\equiv N$) together with counts $L^A,L^B$ of discarded items. Suppose they are ordered as in (3.1):
--   $$\sum_{i=m}^{b}Q^A_i+L^A\le\sum_{i=m}^{b}Q^B_i+L^B\qquad\text{for every } m\ge 1 .$$
--   Apply one step of $\mathrm{Rule}(n_A,n_B,k)$ with $n_A\le n_B$:
--   1. either an item is removed from the $k$-th ordered stack of both ensembles ($1\le k\le N$; nothing happens to an empty stack), by (3.2);
--   2. or an item is added to the $n_A$-th ordered stack of $A$ and to the $n_B$-th ordered stack of $B$ ($1\le n_A\le n_B\le N$), and discarded into $L$ if that stack is full, by (3.3).
--
--   Then the updated ensembles again satisfy (3.1) for every $m\ge 1$.
--
--   Iterating, the ordering is preserved at every step whenever the rule is followed with $n_A\le n_B$. This deterministic statement is the engine of the stochastic comparisons of §3.2.
--
--   **Formalization Note** The printed statement says "for all $m\le b$". For finite $b$ the proof uses (3.5) at $m+1=b+1$, i.e. $L^A\le L^B$, and without it the claim fails at $m=b$ (one stack, $b=1$, $Q^A_1=0$, $L^A=1$, $Q^B_1=1$, $L^B=0$, a removal). The formal statement therefore orders all levels $m\ge 1$, where for $m>b$ the sums are empty; in every application $L^A(0)=L^B(0)=0$, so the extra levels hold at time $0$.
-- source:
--   Mukherjee, Borst, van Leeuwaarden & Whiting, Universality of Power-of-d Load Balancing in Many-Server Systems, arXiv:1612.00723v2, pp. 10–12, Proposition 3.1, (3.1)–(3.3), Rule(n_A, n_B, k)

import Mathlib
import Definitions.Def_PowerOfDUniversality_Fluid_Model
import Definitions.Def_PowerOfDUniversality_Fluid_FluidSpace

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace PowerOfDUniversality.Fluid

/-- **Proposition 3.1** (p. 11, deterministic stack ordering). Let `A` and `B` be ensembles of
`N` stacks with maximum height `b` (occupancy vectors plus discarded items) that are ordered as
in (3.1): `∑_{i=m}^{b} Q^A_i + L^A ≤ ∑_{i=m}^{b} Q^B_i + L^B` for every `m ≥ 1`. After one step of
`Rule(n_A, n_B, k)` with `n_A ≤ n_B` (an item removed from the `k`-th ordered stack of both, or an
item added to the `n_A`-th ordered stack of `A` and the `n_B`-th of `B`), the ordering still
holds for every `m ≥ 1`. -/
theorem proposition_3_1 (N : ℕ) (hN : 1 ≤ N) (b : ℕ∞) (hb : 1 ≤ b) (A B : Ensemble)
    (hA : IsOccupancy N b A.Q) (hB : IsOccupancy N b B.Q) (hAB : StackOrdered A B) :
    (∀ k : ℕ, 1 ≤ k → k ≤ N → StackOrdered (removeItem N k A) (removeItem N k B)) ∧
    (∀ nA nB : ℕ, 1 ≤ nA → nA ≤ nB → nB ≤ N →
      StackOrdered (addItem N b nA A) (addItem N b nB B)) := by sorry

end PowerOfDUniversality.Fluid
