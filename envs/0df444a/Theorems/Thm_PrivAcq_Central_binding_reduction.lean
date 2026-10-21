-- Prove2me | Theorems.Thm_PrivAcq_Central_binding_reduction
-- name    : PrivAcq.Central.binding_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:26:22.737172+00:00
-- url     : https://prove2.me/theorems/2a64514d-3e69-4fb3-9ad2-89479fda843e
-- title:
--   Proof of Theorem 3, pp. 44–45 — the constraints $\eta w_i \le \varepsilon_i$ of (24) bind, reducing it to (A36) = (23)
-- statement:
--   Fix the model under the standing assumptions and a type profile $c$ in the type space. Consider the pointwise problem (24): minimize
--   $$
--   \frac{2(n+1)}{\eta^2} + \sum_{i=1}^n \Big((n+1)\,\mathrm{VAR}\,w_i^2 + \psi_i(c_i)\,\varepsilon_i\Big)
--   $$
--   over $\eta > 0$, $w \ge 0$ with $\sum_i w_i = 1$ and $\eta w_i \le \varepsilon_i$. Then:
--
--   1. for every feasible $(w, \eta, \varepsilon)$, the vector $y = \eta w$ is feasible for (23) and $\mathrm{obj}_{23}(c, y)$ is at most the objective of (24) at $(w,\eta,\varepsilon)$;
--   2. for every $y$ feasible for (23) (that is, $y \ge 0$, $\sum_j y_j > 0$), the triple $w = y/\sum_j y_j$, $\eta = \sum_j y_j$, $\varepsilon = y$ is feasible for (24) with $\eta w = \varepsilon$ and its objective equals $\mathrm{obj}_{23}(c, y)$.
--
--   Hence (24) and (23) have the same value and correspond via $\varepsilon = y$, $\eta = \sum_j y_j$, $w = y/\sum_j y_j$: the step of the proof of Theorem 3 where the constraints $\eta w_i(c) \le \varepsilon_i(c)$ are shown to bind.
--
--   **Formalization Note** The term $(n+1)\,\mathrm{VAR}\,(y_i/\sum_j y_j)^2$ summed with $2(n+1)/(\sum_j y_j)^2$ is (A36); its equality with the objective of (23) is part of item 2.
-- source:
--   Fallah, Makhdoumi, Malekian, Ozdaglar, arXiv:2201.03968v2, p. 19, (24); proof of Theorem 3, pp. 44–45, (A36)

import Mathlib
import Definitions.Def_PrivAcq_Central_Model

namespace PrivAcq.Central

theorem binding_reduction {n : ℕ} (S : Setting n) (hS : S.Standing) (c : Fin n → ℝ)
    (hc : c ∈ S.types) :
    (∀ (w ε : Fin n → ℝ) (η : ℝ), 0 < η → (∀ i, 0 ≤ w i) → ∑ i, w i = 1 →
      (∀ i, η * w i ≤ ε i) →
        (fun i => η * w i) ∈ (feas23 : Set (Fin n → ℝ)) ∧
        obj23 S c (fun i => η * w i) ≤
          2 * ((n : ℝ) + 1) / η ^ 2 +
            ∑ i, (((n : ℝ) + 1) * S.var * (w i) ^ 2 + S.ψ i (c i) * ε i)) ∧
    (∀ y ∈ (feas23 : Set (Fin n → ℝ)),
      0 < ∑ j, y j ∧ (∀ i, 0 ≤ y i / ∑ j, y j) ∧ ∑ i, y i / ∑ j, y j = 1 ∧
        (∀ i, (∑ j, y j) * (y i / ∑ j, y j) = y i) ∧
        2 * ((n : ℝ) + 1) / (∑ j, y j) ^ 2 +
            ∑ i, (((n : ℝ) + 1) * S.var * (y i / ∑ j, y j) ^ 2 + S.ψ i (c i) * y i) =
          obj23 S c y) := by sorry

end PrivAcq.Central
