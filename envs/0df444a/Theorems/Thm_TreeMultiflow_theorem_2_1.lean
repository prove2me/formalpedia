-- Prove2me | Theorems.Thm_TreeMultiflow_theorem_2_1
-- name    : TreeMultiflow.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:01:23.771293+00:00
-- url     : https://prove2.me/theorems/ee52d95b-2c9a-43bb-aba1-44f0fc487ab6
-- title:
--   Theorem 2.1 (Könemann–Parekh–Pritchard), existence part: rounding with additive violation two (time bound: theorem_2_1_polytime)
-- statement:
--   Let $T$ be a tree with positive integer capacities $c_e$, and let $F$ be a finite collection of unit-demand requests with **nonempty** paths (the two endpoints of every request differ) and nonnegative weights $w_f$. Let $x$ be a fractional solution satisfying
--   $$
--   0\le x_f\le 1\ \text{for every } f,\qquad \sum_{f:\ e\in\mathrm{Path}(f)} x_f\le c_e\ \text{for every } e.
--   $$
--   Then there is a subset $J$ of the requests such that
--   $$
--   \sum_{f\in J} w_f\ \ge\ \sum_f w_f x_f\qquad\text{and}\qquad \bigl|\{f\in J : e\in\mathrm{Path}(f)\}\bigr|\le c_e+2\ \text{for every } e.
--   $$
--   Because requests are labeled, the theorem also applies when several requests use the same path.
--
--   This is the bicriteria rounding theorem that the reduction of Section 2 applies to the instance with four copies of every request and capacities $4u_e$. This item is the existence part of Theorem 2.1; the polynomial-time part is the companion item `TreeMultiflow.theorem_2_1_polytime`.
--
--   Differences from the source:
--   - generalization: a tree T = (V, E) (finite) → any vertex type V, no Fintype V; reason: finitely many requests use finitely many edges; the statement for finite V is the paper's
--   - encoding: a finite collection F of labeled requests, Path(f) the unique tree path, capacities u_e on the edges → a Fintype index type F with endpoint maps src, dst; e ∈ Path(f) as OnPath (an edge of the IsPath walk); u : Sym2 V → ℕ constrained only on G.edgeSet; reason: Lean convention; same instances
--   - encoding: nonempty paths → src f ≠ dst f for every request f; reason: in a tree the path between two vertices is empty exactly when they coincide; same instances
-- source:
--   Harb, Improved Integrality Gap for Multicommodity Flow on Trees, arXiv:2609.07949, Theorem 2.1, p.4

import Mathlib
import Definitions.Def_TreeMultiflow_OnPath
import Definitions.Def_TreeMultiflow_load
import Definitions.Def_TreeMultiflow_IsLPFeasible

namespace TreeMultiflow

/-- **Theorem 2.1 (Könemann–Parekh–Pritchard), existence: rounding with additive violation two.**
Harb, *Improved Integrality Gap for Multicommodity Flow on Trees*, arXiv:2609.07949, Theorem 2.1,
p.4: "Consider unit-demand requests with nonempty paths in a tree with positive integer capacities
cₑ and nonnegative weights w_f. Let x be a fractional solution satisfying 0 ≤ x_f ≤ 1 for every f,
Σ_{f : e∈Path(f)} x_f ≤ cₑ for every e. One can find, in polynomial time, a subset J of the
requests such that Σ_{f∈J} w_f ≥ Σ_f w_f x_f and |{f ∈ J : e ∈ Path(f)}| ≤ cₑ + 2 for every e."
"Because requests are labeled, the theorem also applies when several requests use the same path."
(p.4). This item is the existence part; the polynomial-time part is `theorem_2_1_polytime`.

**Formalization Note.** The tree is `G : SimpleGraph V` with `G.IsTree`, on any vertex type.
Requests are a finite index type `F` with endpoints `src`, `dst`; "nonempty paths" is
`src f ≠ dst f`. Capacities `c : Sym2 V → ℕ` are constrained (`≥ 1`) on edges only. -/
theorem theorem_2_1 {V F : Type*} [Fintype F] (G : SimpleGraph V) (hG : G.IsTree)
    (c : Sym2 V → ℕ) (hc : ∀ e ∈ G.edgeSet, 1 ≤ c e) (src dst : F → V)
    (hne : ∀ f, src f ≠ dst f) (w : F → ℝ) (hw : ∀ f, 0 ≤ w f) (x : F → ℝ)
    (hx : IsLPFeasible G c src dst x) :
    ∃ J : Finset F, ∑ f, w f * x f ≤ ∑ f ∈ J, w f ∧
      ∀ e ∈ G.edgeSet, load G src dst J e ≤ c e + 2 := by sorry

end TreeMultiflow
