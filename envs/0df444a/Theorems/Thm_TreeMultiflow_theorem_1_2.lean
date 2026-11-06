-- Prove2me | Theorems.Thm_TreeMultiflow_theorem_1_2
-- name    : TreeMultiflow.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:04:21.941981+00:00
-- url     : https://prove2.me/theorems/61ed4240-5733-4cff-8737-21cacc4b4859
-- title:
--   Theorem 1.2: every feasible LP solution rounds, in polynomial time, to a feasible request set keeping $2/5$ of its value; the integrality gap is at most $5/2$
-- statement:
--   Let $T$ be a tree with integer capacities $u_e\ge 1$, and let $F$ be a finite collection of labeled requests with nonnegative weights $w_f$, request $f$ using the unique tree path $\mathrm{Path}(f)$ between its endpoints. Then:
--
--   1. **(Rounding.)** For every feasible solution $x$ of (1) there is a feasible subset $S\subseteq F$ of requests such that
--   $$
--   w(S)\ \ge\ \frac25\sum_{f\in F} w_f x_f .
--   $$
--   2. **(Integrality gap.)** Consequently, the integrality gap is at most $5/2$:
--   $$
--   \mathrm{LP}^*\le \frac52\,\mathrm{IP}^* .
--   $$
--   3. **(Polynomial time.)** For rationally encoded inputs, such a subset can be found in polynomial time.
--
--   This improves the factor $1/4$ (gap $4$) of Chekuri, Mydlarz and Shepherd, and applies to arbitrary nonnegative weights and arbitrary positive integer capacities, including capacity-one edges next to larger ones.
--
--   **Formalization Note** The integrality gap clause is stated as $\mathrm{LP}^*\le\frac52\mathrm{IP}^*$ for every instance. Polynomial time is Mathlib's `Turing.TM2ComputableInPolyTime` over a binary encoding of the tree, the capacities, the requests and the fractional solution.
--
--   Differences from the source:
--   - generalization: a tree T = (V, E) (finite) → any vertex type V, no Fintype V; reason: finitely many requests use finitely many edges; the statement for finite V is the paper's
--   - encoding: the integrality gap (worst-case ratio LP*/IP* over instances with positive LP optimum) is at most 5/2 → lpOpt ≤ (5/2) · ipOpt for every instance; reason: for LP* > 0 the two are equivalent (IP* > 0 is then forced), and for LP* = 0 the inequality holds since IP* ≥ 0; avoids x / 0 = 0
--   - reading: such a subset can be found in polynomial time for rationally encoded inputs → ∃ alg with Nonempty (Turing.TM2ComputableInPolyTime encRatInstance id alg), correct on every well-formed instance with LP-feasible x; reason: the standard Turing-machine reading; numbers are binary, x is part of the input, and well-formedness excludes only inputs that are not trees with capacities ≥ 1 and weights ≥ 0
--   - encoding: a finite collection F of labeled requests, Path(f) the unique tree path, capacities u_e on the edges → a Fintype index type F with endpoint maps src, dst; e ∈ Path(f) as OnPath (an edge of the IsPath walk); u : Sym2 V → ℕ constrained only on G.edgeSet; reason: Lean convention; same instances
--   - encoding: rationally encoded inputs (tree, capacities, weights, x) and the subset S as the output → a RatInstance with vertices Fin (n + 1), read through RatInstance.graph/cap/src/dst/weight/lpval and the same IsLPFeasible and IsFeasible as clause (A); output a Boolean mask alg I : List Bool, with f ∈ S iff (alg I).getD f false = true; reason: every finite tree has such a labeling, and a mask of length |F| is the usual output encoding of a subset; same instances
-- source:
--   Harb, Improved Integrality Gap for Multicommodity Flow on Trees, arXiv:2609.07949, Theorem 1.2, p.3

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_TreeMultiflow_IsFeasible
import Definitions.Def_TreeMultiflow_IsLPFeasible
import Definitions.Def_TreeMultiflow_lpOpt
import Definitions.Def_TreeMultiflow_ipOpt
import Definitions.Def_TreeMultiflow_RatInstance
import Definitions.Def_TreeMultiflow_RatInstance_graph
import Definitions.Def_TreeMultiflow_RatInstance_cap
import Definitions.Def_TreeMultiflow_RatInstance_src
import Definitions.Def_TreeMultiflow_RatInstance_dst
import Definitions.Def_TreeMultiflow_RatInstance_weight
import Definitions.Def_TreeMultiflow_RatInstance_lpval
import Definitions.Def_TreeMultiflow_RatInstance_WellFormed
import Definitions.Def_TreeMultiflow_encRatInstance

universe u₁ u₂

namespace TreeMultiflow

/-- **Theorem 1.2: 2/5 rounding, integrality gap at most 5/2, in polynomial time.**
Harb, *Improved Integrality Gap for Multicommodity Flow on Trees*, arXiv:2609.07949, Theorem 1.2,
p.3: "For every feasible solution x of (1), there is a feasible subset S ⊆ F of requests such that
w(S) ≥ (2/5) Σ_{f∈F} w_f x_f. Consequently, the integrality gap is at most 5/2. Moreover, for
rationally encoded inputs, such a subset can be found in polynomial time."
Setting (p.2): a tree with integer capacities uₑ ≥ 1, a finite collection of labeled requests with
nonnegative weights, each with the unique tree path between its endpoints.

The three clauses:

* **(A)** for every tree `G` with capacities `u ≥ 1` on its edges, labeled requests `F` with
  endpoints `src`, `dst`, weights `w ≥ 0`, and every feasible solution `x` of (1), some feasible
  `S` has `Σ_{f∈S} w f ≥ (2/5) Σ_f w f x f`;
* **(B)** for the same data, the LP optimum is at most `5/2` times the integral optimum;
* **(C)** some map `alg`, computable by a Turing machine in time polynomial in the length of the
  binary encoding `encRatInstance`, returns on every well-formed rational instance with a
  feasible `x` a mask of a set `S` with the property of (A).

**Formalization Note.** The vertex type is arbitrary (no `Fintype V`); finitely many requests
use only finitely many edges, and the finite case is the paper's. The gap clause is stated as
`lpOpt ≤ (5/2) · ipOpt` for every instance, which is the bound on the ratio over instances with
positive LP optimum (and avoids `x / 0 = 0`). Polynomial time is `Turing.TM2ComputableInPolyTime`
over the alphabet `OnlineCRS.Combine.Sym` with binary numbers; the fractional solution is part of
the input; the output mask is read with `getD … false`. Correctness in (C) uses the same
`IsLPFeasible` and `IsFeasible` as (A), on the instance decoded by `RatInstance.graph`, `cap`,
`src`, `dst`, `weight`, `lpval`. -/
theorem theorem_1_2 :
    (∀ (V : Type u₁) (F : Type u₂) [Fintype F] (G : SimpleGraph V), G.IsTree →
      ∀ u : Sym2 V → ℕ, (∀ e ∈ G.edgeSet, 1 ≤ u e) →
      ∀ (src dst : F → V) (w : F → ℝ), (∀ f, 0 ≤ w f) →
      ∀ x : F → ℝ, IsLPFeasible G u src dst x →
        ∃ S : Finset F, IsFeasible G u src dst S ∧
          (2 / 5 : ℝ) * ∑ f, w f * x f ≤ ∑ f ∈ S, w f) ∧
    (∀ (V : Type u₁) (F : Type u₂) [Fintype F] (G : SimpleGraph V), G.IsTree →
      ∀ u : Sym2 V → ℕ, (∀ e ∈ G.edgeSet, 1 ≤ u e) →
      ∀ (src dst : F → V) (w : F → ℝ), (∀ f, 0 ≤ w f) →
        lpOpt G u src dst w ≤ (5 / 2 : ℝ) * ipOpt G u src dst w) ∧
    (∃ alg : RatInstance → List Bool,
      Nonempty (Turing.TM2ComputableInPolyTime encRatInstance (fun m : List Bool => m) alg) ∧
      ∀ I : RatInstance, I.WellFormed → IsLPFeasible I.graph I.cap I.src I.dst I.lpval →
        IsFeasible I.graph I.cap I.src I.dst
            (Finset.univ.filter fun f : Fin I.reqs.length => (alg I).getD f false = true) ∧
          (2 / 5 : ℝ) * ∑ f, I.weight f * I.lpval f ≤
            ∑ f ∈ Finset.univ.filter (fun f : Fin I.reqs.length => (alg I).getD f false = true),
              I.weight f) := by sorry

end TreeMultiflow
