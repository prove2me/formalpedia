-- Prove2me | Theorems.Thm_RobustMNL_Dynamic_revenue_ordered_robust
-- name    : RobustMNL.Dynamic.revenue_ordered_robust
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:21:23.085987+00:00
-- url     : https://prove2.me/theorems/492cc33a-dcf2-4d8a-b967-868a44d0b7fa
-- title:
--   Theorem 3.2 (restated) — revenue-ordered assortments are robust: S*(V) = {i : rᵢ > Z*(V)}
-- statement:
--   Let $\mathcal V \subseteq \mathbb R^{n+1}_{++}$ be a compact nonempty uncertainty set and let $r_1, \dots, r_n$ be arbitrary real revenues. An assortment $S$ is an optimal assortment of the Robust Logit problem with the smallest cardinality among optimal assortments if and only if
--   $$S = \{\, i \in \mathcal A : r_i > Z^*(\mathcal V) \,\}.$$
--   In particular the threshold set is optimal, and it is the unique optimal assortment of smallest cardinality.
--
--   The robust assortment is therefore revenue-ordered, exactly as in the case of known parameters. In Section 4 this is applied period by period with revenues $r_i - \Delta J_{t+1}(x)$.
--
--   **Formalization Note** The paper writes "$V \subset \mathbb R^n_{++}$"; the parameter vector has $n+1$ components and the standing assumption of Sec. 3 is a compact $V \subseteq \mathbb R^{n+1}_{++}$, which is stated here (with nonemptiness, implicit in $\min_{v\in V}$). The theorem is stated for arbitrary real revenues; the paper's ordering $r_1 \ge \dots \ge r_n > 0$ is "without loss of generality", is used by no step of the proof, and Section 4 needs revenues $r_i - \Delta J_{t+1}(x)$ that may be negative. $S^*(\mathcal V)$ is the predicate `IsSmallestOptimal`; the "↔" asserts both that every such $S$ is the threshold set and that the threshold set is one. This restates `RobustMNL.Static.revenue_ordered_robust` of the companion mission verbatim up to namespace.
-- source:
--   Rusmevichientong, Topaloglu, Robust Assortment Optimization in Revenue Management Under the Multinomial Logit Choice Model, Operations Research (2012), doi:10.1287/opre.1120.1063, authors' manuscript of 20 Sep 2011, Theorem 3.2, p. 7

import Mathlib
import Definitions.Def_RobustMNL_Dynamic_StaticModel

namespace RobustMNL.Dynamic

theorem revenue_ordered_robust {n : ℕ} (r : Fin n → ℝ) (V : Set (ℝ × (Fin n → ℝ)))
    (hV : IsCompact V) (hne : V.Nonempty) (hpos : ∀ p ∈ V, RobustMNL.Static.IsPos p) (S : Finset (Fin n)) :
    RobustMNL.Static.IsSmallestOptimal V r S ↔ S = Finset.univ.filter (fun i => RobustMNL.Static.Zstar V r < r i) := by sorry

end RobustMNL.Dynamic
