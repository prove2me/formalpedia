-- Prove2me | Theorems.Thm_RobustMNL_Static_revenue_ordered_robust
-- name    : RobustMNL.Static.revenue_ordered_robust
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:24:03.493732+00:00
-- url     : https://prove2.me/theorems/78e8a0db-c2dd-4983-98f4-53a14c1e0212
-- title:
--   Theorem 3.2 — Revenue-ordered assortments are robust: S*(𝒱) = {i : rᵢ > Z*(𝒱)}
-- statement:
--   **Revenue-ordered assortments are robust.** Let $\mathcal V \subseteq \mathbb R^{n+1}_{++}$ be a compact nonempty uncertainty set for the parameters of the multinomial logit model, and let $r_1, \dots, r_n$ be the product revenues. An assortment $S \subseteq \mathcal A$ is an optimal solution of the Robust Logit problem
--   $$Z^*(\mathcal V) = \max_{S \subseteq \mathcal A}\ \min_{v\in\mathcal V} f(S, v)$$
--   with the smallest cardinality among all optimal solutions if and only if
--   $$S = \{\, i \in \mathcal A : r_i > Z^*(\mathcal V) \,\}.$$
--   In particular the smallest optimal robust assortment $S^*(\mathcal V)$ is unique, and it consists of the products whose revenue strictly exceeds the optimal worst-case revenue. When the revenues are ordered, $r_1 \ge \dots \ge r_n$, it is therefore one of the $n+1$ revenue-ordered assortments $\{1, \dots, i\}$, so the robust problem needs only these to be searched.
--
--   **Formalization Note** The theorem is stated as an "if and only if" for every assortment $S$: the forward direction is the paper's identity for any choice of $S^*(\mathcal V)$, the backward direction says that the threshold set itself is an optimal assortment of smallest cardinality. The page writes "$\mathcal V \subset \mathbb R^n_{++}$"; the parameter vector has $n+1$ components (p. 5) and $\mathcal V$ is compact by the standing assumption of Sec. 3 (p. 6), which the proof uses, so the statement is made for compact nonempty $\mathcal V \subseteq \mathbb R^{n+1}_{++}$. Revenues are arbitrary reals rather than $r_1 \ge \dots \ge r_n > 0$: the proof uses neither the order nor the sign, and Sec. 4 of the paper applies the theorem to revenues that may be negative. Products are `Fin n` (Lean index $i$ is the paper's product $i+1$).
-- source:
--   Rusmevichientong, Topaloglu, Robust Assortment Optimization in Revenue Management Under the Multinomial Logit Choice Model, Operations Research (2012), doi:10.1287/opre.1120.1063, authors' manuscript of 20 Sep 2011, Theorem 3.2, p. 7

import Mathlib
import Definitions.Def_RobustMNL_Static_Model

namespace RobustMNL.Static

theorem revenue_ordered_robust {n : ℕ} (r : Fin n → ℝ) (V : Set (ℝ × (Fin n → ℝ)))
    (hV : IsCompact V) (hne : V.Nonempty) (hpos : ∀ p ∈ V, IsPos p) (S : Finset (Fin n)) :
    IsSmallestOptimal V r S ↔ S = Finset.univ.filter (fun i => Zstar V r < r i) := by sorry

end RobustMNL.Static
