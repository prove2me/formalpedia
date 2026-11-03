-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_loads_insufficient_on_five
-- name    : QuantumMaxCutEnergy.loads_insufficient_on_five
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T05:07:38.37378+00:00
-- url     : https://prove2.me/theorems/0a9eb986-7a3b-4aa0-8f6f-8d727e5726c2
-- title:
--   Loads alone do not suffice: the $K_5$ point $x\equiv 1/4$ is not dominated by any matching
-- statement:
--   **Loads alone do not suffice: the odd-cycle obstruction on $K_5$.**
--
--   On the complete graph on five vertices take the constant edge weight $x_e=\tfrac14$ for every edge $e$. Then
--
--   * every vertex load equals $1$, i.e. $x$ satisfies *all* the vertex constraints of the fractional matching
--     polytope at equality, and
--   * nevertheless no integral matching carries the total weight: with unit edge weights,
--     $\sum_e w_e x_e=\tfrac{10}{4}$, while $\sum_{e\in M}w_e=|M|\le 2$ for every matching $M$ of $K_5$.
--
--   **Why.** Each of the five vertices is incident with four edges, so its load is $4\cdot\tfrac14=1$; there are ten
--   edges, so the total weight is $\tfrac{10}{4}=\tfrac52$; and a matching of $K_5$ has at most $\lfloor 5/2\rfloor=2$
--   edges.
--
--   **Role.** This is the sharpest form of the statement that the bipartite argument cannot be extended: over a
--   bipartite support the vertex loads alone force domination
--   (`QuantumMaxCutEnergy.matching_dominated_of_bipartite`), but on $K_5$ the point $x=\tfrac14$ satisfies the loads
--   and the triangle constraints while violating only the odd-set constraint for the full five-element set
--   ($\tfrac{10}{4}>2$). That constraint is therefore exactly the odd-cycle information that the general case of
--   Edmonds' exactness needs — and the same point is the tightness example for the $\tfrac45$ dilation of LP24's
--   Lemma 4.
-- source:
--   Lee-Parekh arXiv:2401.03616, Section 2.3 (the tightness example for the 4/5 dilation: K_5 with x = 1/4); Edmonds, J. Res. Nat. Bur. Standards 69B (1965).

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Mathlib
open scoped BigOperators

namespace QuantumMaxCutEnergy

/-- **Loads alone do not suffice** (and the odd-cycle obstruction is real): on the complete graph on five
vertices the constant edge weight `x = 1/4` has every vertex load equal to `1`, yet no matching carries its
total weight `10/4`. -/
theorem loads_insufficient_on_five :
    (∀ v : Fin 5, loadAt (fun _ : Edge 5 => (1 / 4 : ℝ)) v ≤ 1) ∧
    (∀ M : Finset (Edge 5),
      (∀ e ∈ M, ∀ e' ∈ M, e ≠ e' →
        e.val.1 ≠ e'.val.1 ∧ e.val.1 ≠ e'.val.2 ∧ e.val.2 ≠ e'.val.1 ∧ e.val.2 ≠ e'.val.2) →
      (∑ e ∈ M, (1 : ℝ)) < ∑ e : Edge 5, (1 : ℝ) * (1 / 4)) := by sorry

end QuantumMaxCutEnergy
