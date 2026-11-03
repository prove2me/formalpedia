-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_matching_balanced_split
-- name    : QuantumMaxCutEnergy.matching_balanced_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T01:51:33.535789+00:00
-- url     : https://prove2.me/theorems/b986d9a1-a604-4fc2-9387-4642842b578a
-- title:
--   Balanced split: a circulation perturbation of a load-polytope point with smaller support
-- statement:
--   **Balanced split of a point of the fractional matching polytope.**
--
--   Let $G$ be a graph on $n$ vertices, $x\ge0$ a weight on its edges whose vertex loads
--   $\mathrm{load}_x(v)=\sum_{e\ni v}x_e$ are all at most $1$, and let $A,B$ be two disjoint nonempty finite
--   sets of edges that are *locally balanced*: at every vertex $v$,
--   $$\#\{e\in A: v\in e\}\;=\;\#\{e\in B: v\in e\}.$$
--   (Equivalently, the edge weight $\mathbf 1_B-\mathbf 1_A$ has zero load at every vertex — it is a
--   circulation on the support graph; the alternating classes of an even cycle are the basic example.)
--
--   **Theorem.** There are points $y,z$ of the polytope (nonnegative, all loads at most $1$) and a
--   $\lambda\in[0,1]$ with
--   $$x=\lambda\,y+(1-\lambda)\,z,$$
--   such that $y$ vanishes on some edge of $A$ and $z$ vanishes on some edge of $B$; moreover $y$ and $z$ agree
--   with $x$ off $A\cup B$. In particular both $y$ and $z$ have strictly smaller support than $x$ (because
--   $A,B\subseteq\operatorname{supp}x$).
--
--   **Construction.** Move $x$ along the circulation $\mathbf 1_B-\mathbf 1_A$, which leaves every vertex load
--   unchanged, as far as possible in each direction: $y=x+\alpha(\mathbf 1_B-\mathbf 1_A)$ with
--   $\alpha=\min_A x$, and $z=x-\beta(\mathbf 1_B-\mathbf 1_A)$ with $\beta=\min_B x$. Then $x$ is the convex
--   combination of $y$ and $z$ with weight $\beta/(\alpha+\beta)$, and an edge of $A$ (resp. of $B$) attains its
--   minimum, so the corresponding coordinate vanishes.
--
--   **Role.** This is the perturbation step of Edmonds' exactness of the matching polytope
--   (`QuantumMaxCutEnergy.matching_polytope_integral_rounding`). Applied at a maximiser of a linear objective, it
--   either exhibits a strictly better pair of sub-points or forces the support to be acyclic; with the odd-set
--   constraints killing the odd cycles, what survives is an integral matching. It is the bipartite-case engine too,
--   where every cycle is even. The statement deliberately mentions no cycle: local balance is the only property
--   the argument uses, which keeps the bookkeeping inside `Finset` sums.
--
--   **Formalization.** The Lean proof works with the published load `QuantumMaxCutEnergy.loadAt`, shows that loads
--   are additive under a pointwise perturbation, computes the load of a `0/1` edge weight as a degree
--   (`Finset.sum_boole`), and then verifies nonnegativity and the convex-combination identity for the two extreme
--   steps.
-- source:
--   Edmonds, J. Res. Nat. Bur. Standards 69B (1965); Schrijver, Combinatorial Optimization, Ch. 25 (odd-set polytope); the perturbation is the standard half-integrality argument behind the blossom inequalities.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Mathlib
open scoped BigOperators

namespace QuantumMaxCutEnergy

/-- **Balanced split of a load-polytope point.**

Let `x ≥ 0` be an edge weight with all vertex loads at most `1`, and let `A`, `B` be disjoint
nonempty finite sets of edges that are *locally balanced*: at every vertex, as many edges of `A` as
of `B` are incident. Then `x` is a convex combination of two points `y`, `z` of the load polytope,
each of which has strictly smaller support: `y` vanishes on some edge of `A`, `z` on some edge of
`B`. The two points differ from `x` only on `A ∪ B`.

This is the perturbation step of Edmonds' exactness: the direction `1_B - 1_A` is a circulation (it
leaves every vertex load unchanged), so moving `x` along it as far as nonnegativity allows produces
the endpoints of a segment through `x` inside the polytope. -/
theorem matching_balanced_split {n : ℕ} (x : Edge n → ℝ) (A B : Finset (Edge n))
    (hx : ∀ e, 0 ≤ x e) (hload : ∀ v, loadAt x v ≤ 1)
    (hApos : ∀ e ∈ A, 0 < x e) (hBpos : ∀ e ∈ B, 0 < x e)
    (hA : A.Nonempty) (hB : B.Nonempty) (hdisj : Disjoint A B)
    (hbal : ∀ v : Fin n,
      (A.filter (fun e => v = e.val.1 ∨ v = e.val.2)).card
        = (B.filter (fun e => v = e.val.1 ∨ v = e.val.2)).card) :
    ∃ (y z : Edge n → ℝ) (lam : ℝ),
      (∀ e, 0 ≤ y e) ∧ (∀ v, loadAt y v ≤ 1) ∧
      (∀ e, 0 ≤ z e) ∧ (∀ v, loadAt z v ≤ 1) ∧
      0 ≤ lam ∧ lam ≤ 1 ∧
      (∀ e, x e = lam * y e + (1 - lam) * z e) ∧
      (∃ e, x e ≠ 0 ∧ y e = 0) ∧ (∃ e, x e ≠ 0 ∧ z e = 0) := by sorry

end QuantumMaxCutEnergy
