-- Prove2me | Theorems.Thm_RobustMNL_Dynamic_optAssort_iff_static
-- name    : RobustMNL.Dynamic.optAssort_iff_static
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:22:16.32099+00:00
-- url     : https://prove2.me/theorems/23af033b-d401-4721-851e-89ae10588c9f
-- title:
--   Proof of Theorem 4.2, pp. 16–17 — S*_t(x) solves the static robust problem with revenues r_i − ΔJ_{t+1}(x)
-- statement:
--   Let $1 \le t \le T$ and $x \ge 1$, and write $\tilde r_i = r_i - \Delta J_{t+1}(x)$. Then:
--
--   1. An assortment $S$ is an optimal assortment of smallest cardinality of the period-$t$ Bellman problem with capacity $x$ (that is, $S = S^*_t(x)$) if and only if $S$ is an optimal assortment of smallest cardinality of the static Robust Logit problem over $\mathcal V_t$ with revenues $\tilde r$ (that is, $S = S^*(\mathcal V_t)$ for revenues $\tilde r$).
--   2. The optimal values agree:
--   $$J_t(x) - J_{t+1}(x) = \max_{S \subseteq \mathcal A}\ \min_{v \in \mathcal V_t} \sum_{i\in S} \phi_i(S, v)\,\big(r_i - \Delta J_{t+1}(x)\big) = Z^*(\mathcal V_t)\big|_{\text{revenues } \tilde r}.$$
--
--   This is the reduction by which every structural result of Section 3 transfers to the dynamic problem.
--
--   **Formalization Note** The static objects are the restated `IsSmallestOptimal` and `Zstar` at the revenues `fun i => r i - marginalValue T V r (t + 1) x`. The paper's remark that products with $r_i < \Delta J_{t+1}(x)$ are never used is not needed, since the static results are stated for arbitrary real revenues.
-- source:
--   Rusmevichientong, Topaloglu, Robust Assortment Optimization in Revenue Management Under the Multinomial Logit Choice Model, Operations Research (2012), doi:10.1287/opre.1120.1063, authors' manuscript of 20 Sep 2011, Proof of Theorem 4.2, p. 16 (last display) – p. 17 (first paragraph)

import Mathlib
import Definitions.Def_RobustMNL_Dynamic_ValueFunction

namespace RobustMNL.Dynamic

theorem optAssort_iff_static {n : ℕ} (T : ℕ) (V : ℕ → Set (ℝ × (Fin n → ℝ)))
    (r : Fin n → ℝ) (hV : IsUncertaintySeq T V) (t x : ℕ) (ht : 1 ≤ t) (htT : t ≤ T) (hx : 1 ≤ x) :
    (∀ S : Finset (Fin n), IsOptAssort T V r t x S ↔
        RobustMNL.Static.IsSmallestOptimal (V t) (fun i => r i - marginalValue T V r (t + 1) x) S) ∧
      J T V r t x - J T V r (t + 1) x =
        RobustMNL.Static.Zstar (V t) (fun i => r i - marginalValue T V r (t + 1) x) := by sorry

end RobustMNL.Dynamic
