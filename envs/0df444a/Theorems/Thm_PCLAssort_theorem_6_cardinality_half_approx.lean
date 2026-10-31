-- Prove2me | Theorems.Thm_PCLAssort_theorem_6_cardinality_half_approx
-- name    : PCLAssort.theorem_6_cardinality_half_approx
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:23:05.751871+00:00
-- url     : https://prove2.me/theorems/77999b07-6aae-4b21-aafb-02cae770da7a
-- title:
--   Theorem 6 — Algorithm 1 is a 0.5-approximation for cardinality-constrained max-dicut and PCL assortment optimization
-- statement:
--   Algorithm 1 gives a 0.5-approximation algorithm for max-dicut with a cardinality constraint relative to the LP (9). Hence there is a 0.5-approximation algorithm for the cardinality-constrained PCL assortment optimization problem. Precisely:
--
--   1. **(max-dicut)** Let $(V,E)$ be a finite directed graph without loops with weights $w_{ij}\ge 0$, let $c\in\mathbb N$ and let all sizes be $1$. Let $(x,y)$ be any optimal basic solution of LP (9), with optimal value $LP^*$. Then Algorithm 1 run from $(x,y)$ has an output, and every output $T$ satisfies $|T|\le c$ and
--
--   $$
--   \mathrm{cut}(T)\ge 0.5\cdot LP^*.
--   $$
--
--   2. **(PCL assortment)** Let a PCL instance and $c\in\mathbb N$ be given, and let $g$ be the optimal value of LP$(z)$ for the cardinality family. Then $g(\cdot)/v_0$ has a fixed point $\hat z\ge0$. For every fixed point $\hat z$, the LP (9) on $\tilde G_{\hat z}$ (all $n+1$ vertices of size $1$, capacity $c$) has an optimal basic solution from which Algorithm 1 has an output; and for every optimal basic solution and every output $T$, the assortment $S=\{i\in[n]: i\in T,\ r_i\ge\hat z\}$ satisfies $|S|\le c$ and
--
--   $$
--   \pi(S)\ge 0.5\cdot z^*,
--   $$
--
--   where $z^*$ is the optimal revenue over assortments with at most $c$ products.
--
--   Zhang et al. (2020) had a factor $0.25$ for this problem.
--
--   Differences from the source:
--   - encoding: Algorithm 1 gives an approximation algorithm (polynomial time) → Algorithm 1 as an output relation: an output exists, and every output satisfies the bound; running time not formalized; reason: the procedure is two LP solves and at most |V| − 1 pipage steps over the reals; the structural content is kept and every nondeterministic choice is covered
--   - reading: §4.2 step 4: round the LP(ẑ) solution x̄ on G̃_ẑ (the dummy vertex has x_{n+1} = 0, not in the knapsack) → Algorithm 1 on G̃_ẑ with all n + 1 vertices of size 1 and capacity c; the assortment is T ∩ {i ∈ [n] : r_i ≥ ẑ}; reason: the page identifies LP (9) with LP(z) without saying how the dummy enters; LP(ẑ)-feasible points are feasible here, and dropping vertices with r_i < ẑ (Lemma 7) and the dummy never lowers the cut
--   - encoding: ẑ obtained by solving (D) (Lemma 9) → every ẑ with g(ẑ) = v₀ẑ; reason: the fixed point is unique (g − v₀z is strictly decreasing) and Lemma 9's ẑ is one
--   - encoding: LP* = optimal value of LP (9) → the objective value of the given optimal solution (x, y); reason: equal by optimality
--   - reading: a directed graph (V, E) → a digraph without loops (e.1 ≠ e.2 for e ∈ E); reason: the paper's graphs G_z, G̃_z have no loops, and F(x) = Σ w_ij x_i(1 − x_j) agrees with the cut only without loops
--   - encoding: basic feasible solution of LP (9) → extreme point of the feasible polytope in the joint (x, y) space; reason: for a polyhedron, basic feasible solutions are exactly its extreme points
--   - encoding: y ∈ ℝ^E → y : V × V → ℝ with y = 0 off E; reason: a linear copy of the same polytope; feasibility, objective and extreme points correspond
--   - reading: v₀ is the no-purchase weight, with no sign stated (p.789) → v₀ > 0 (field of PCLInstance); reason: the paper divides by v₀ (fixed point of g(·)/v₀, p.792); with v₀ = 0 the framework degenerates
--   - encoding: γ_ij ∈ [0, 1] (p.789) → γ_ij ∈ (0, 1] for i ≠ j; reason: v_i^{1/γ_ij} is undefined at γ_ij = 0; this excludes only the undefined case
--   - encoding: R_ij(x) = 0/0 for an empty nest → Lean's 0/0 = 0; reason: the nest then has weight V_ij(x)^{γ_ij} = 0 (γ_ij > 0), so it contributes nothing either way
--   - encoding: vertices [n+1] with dummy n+1, products [n] → Option (Fin n) with none the dummy, Fin n; reason: relabelling; same graph
--   - reading: edge weights (4)–(6), whose ξ⁻/ψ⁻ subscripts disagree with the prose on pp.790–791 → closed forms: the pair (i,j) puts r̄_i a/D on (i,n+1), r̄_j b/D on (j,n+1), v_i r̄_i − r̄_i a/D on (i,j), v_j r̄_j − r̄_j b/D on (j,i); reason: the closed forms are unambiguous and make Lemma 1 hold; the subscripts are a typesetting inconsistency
--   - reading: edge weights w : E → ℝ (Definition 1: "usually assumed" nonnegative) → 0 ≤ w e for e ∈ E; reason: p.794: "it suffices to consider instances with nonnegative edge-weights"; Algorithm 1 is stated for that setting (G̃_z)
--   - encoding: knapsack Σ_{i∈[n]} s_i x_i ≤ c in (9), with x_i ≤ 1 for i ∈ V → Σ over all i ∈ V; reason: for a generic graph V = [n]; same constraint
--   - encoding: c, the limit on the number of products → c : ℕ cast to ℝ; reason: a cardinality limit is a natural number
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), Theorem 6, p.795 (PDF p.11)

import Mathlib
import Definitions.Def_PCLAssort_cutValue
import Definitions.Def_PCLAssort_LP9Feasible
import Definitions.Def_PCLAssort_LP9Objective
import Definitions.Def_PCLAssort_IsLP9Optimal
import Definitions.Def_PCLAssort_Alg1Output
import Definitions.Def_PCLAssort_PCLInstance
import Definitions.Def_PCLAssort_revenue
import Definitions.Def_PCLAssort_optRevenue
import Definitions.Def_PCLAssort_cardFamily
import Definitions.Def_PCLAssort_pclWeight
import Definitions.Def_PCLAssort_tildeEdges
import Definitions.Def_PCLAssort_gValue

namespace PCLAssort

/-- Theorem 6 (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, p.795): Algorithm 1 gives a 0.5-approximation algorithm for max-dicut with a
cardinality constraint relative to the LP (9). Hence, there is a 0.5-approximation algorithm for the
cardinality-constrained PCL assortment optimization problem.

(a) For every finite loopless digraph with nonnegative edge weights, every capacity `c ∈ ℕ` and unit
sizes, and every optimal basic solution `(x, y)` of LP (9): Algorithm 1 has an output, and every
output `T` satisfies `|T| ≤ c` and `cut(T) ≥ 0.5 · LP*`, where `LP*` is the optimal value of LP (9).

(b) For every PCL instance and every `c ∈ ℕ`, the procedure of §4.2 (fixed point `ẑ` of `g(·)/v_0`
for the cardinality LP(z), an optimal basic solution of LP (9) on `G̃_ẑ`, Algorithm 1) has an output,
and every output assortment `S` satisfies `|S| ≤ c` and `π(S) ≥ 0.5 · z*`.

**Formalization Note.** Algorithm 1 is the output relation `Alg1Output`; "has an output" is the
existence of a run, and the bound holds for every run. For (b), Algorithm 1 is run on `G̃_ẑ` with
vertex set `[n + 1]` (dummy included), every vertex of size 1 and capacity `c`, and the assortment
returned is `{i ∈ [n] : i ∈ T, r_i ≥ ẑ}` (Lemma 7's `x̄_i = 0` on `N_ẑ`, dummy dropped). `ẑ` ranges
over all fixed points (Lemma 9's `ẑ` is one). Polynomial running time is not formalized. -/
theorem theorem_6_cardinality_half_approx :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (E : Finset (V × V)) (w : V × V → ℝ),
      (∀ e ∈ E, e.1 ≠ e.2) → (∀ e ∈ E, 0 ≤ w e) →
      ∀ (c : ℕ) (p : (V → ℝ) × (V × V → ℝ)),
        p ∈ Set.extremePoints ℝ (LP9Feasible E (fun _ => 1) c) →
        IsLP9Optimal E w (fun _ => 1) c p →
        (∃ T : Finset V, Alg1Output E w (fun _ => 1) c p.1 T) ∧
        ∀ T : Finset V, Alg1Output E w (fun _ => 1) c p.1 T →
          T.card ≤ c ∧ (0.5 : ℝ) * LP9Objective E w p ≤ cutValue E w T) ∧
    (∀ (n : ℕ) (I : PCLInstance n) (c : ℕ),
      (∃ zhat : ℝ, 0 ≤ zhat ∧ gValue I (fun _ => 1) c zhat = I.v0 * zhat) ∧
      ∀ zhat : ℝ, gValue I (fun _ => 1) c zhat = I.v0 * zhat →
        (∃ (p : (Option (Fin n) → ℝ) × (Option (Fin n) × Option (Fin n) → ℝ))
            (T : Finset (Option (Fin n))),
          p ∈ Set.extremePoints ℝ (LP9Feasible (tildeEdges I zhat) (fun _ => 1) c) ∧
          IsLP9Optimal (tildeEdges I zhat) (pclWeight I zhat) (fun _ => 1) c p ∧
          Alg1Output (tildeEdges I zhat) (pclWeight I zhat) (fun _ => 1) c p.1 T) ∧
        ∀ (p : (Option (Fin n) → ℝ) × (Option (Fin n) × Option (Fin n) → ℝ))
            (T : Finset (Option (Fin n))),
          p ∈ Set.extremePoints ℝ (LP9Feasible (tildeEdges I zhat) (fun _ => 1) c) →
          IsLP9Optimal (tildeEdges I zhat) (pclWeight I zhat) (fun _ => 1) c p →
          Alg1Output (tildeEdges I zhat) (pclWeight I zhat) (fun _ => 1) c p.1 T →
            (Finset.univ.filter (fun i : Fin n => some i ∈ T ∧ zhat ≤ I.r i)).card ≤ c ∧
            (0.5 : ℝ) * optRevenue I (cardFamily n c) ≤
              revenue I (Finset.univ.filter (fun i : Fin n => some i ∈ T ∧ zhat ≤ I.r i))) := by sorry

end PCLAssort
