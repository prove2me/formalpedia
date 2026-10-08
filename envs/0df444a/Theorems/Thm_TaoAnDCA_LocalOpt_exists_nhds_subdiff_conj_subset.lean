-- Prove2me | Theorems.Thm_TaoAnDCA_LocalOpt_exists_nhds_subdiff_conj_subset
-- name    : TaoAnDCA.LocalOpt.exists_nhds_subdiff_conj_subset
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:23:05.698583+00:00
-- url     : https://prove2.me/theorems/5846cf4f-fa3f-421e-b2d9-52cb3a788069
-- title:
--   §3.2, proof of Corollary 3.5, p. 485 — upper semicontinuity: V ⊂ int(dom g*) with ∂g*(V) ⊂ U ∩ dom g
-- statement:
--   Let $g, h \in \Gamma_0(\mathbb R^n)$ satisfy the standing inclusions $\operatorname{dom} g \subset \operatorname{dom} h$ and $\operatorname{dom} h^* \subset \operatorname{dom} g^*$. Let $y^* \in \mathbb R^n$ and let $U \subset \mathbb R^n$ be an open set such that
--   $$y^* \in \operatorname{int}(\operatorname{dom} g^*) \quad\text{and}\quad \partial g^*(y^*) \subset U. \tag{12}$$
--   Then $y^*$ has a neighbourhood $V \subset \operatorname{int}(\operatorname{dom} g^*)$ such that
--   $$\partial g^*(y) \subset U \cap \operatorname{dom} g \qquad \text{for every } y \in V;$$
--   in particular $\partial g^*(V) \subset U$.
--
--   This is the upper semicontinuity step of the proof of Corollary 3.5: it turns the pointwise condition (12) at $y^*$ into a condition on a whole neighbourhood of $y^*$, which is what the dual application of Theorem 3.2(ii) needs.
--
--   **Formalization Note.** $U$ is required to be open: upper semicontinuity of $\partial g^*$ gives $\partial g^*(V)$ inside any open set containing $\partial g^*(y^*)$, and (12) supplies such an open set only when $U$ is open. Of the standing assumptions only $g \in \Gamma_0$ matters here.
-- source:
--   Pham Dinh & Le Thi, A d.c. optimization algorithm for solving the trust-region subproblem, SIAM J. Optim. 8 (1998), p. 485, §3.2, proof of Corollary 3.5, third and fourth sentences, with (12)

import Mathlib
import Definitions.Def_TaoAnDCA_LocalOpt_Setting

open Filter Topology

namespace TaoAnDCA.LocalOpt

/-- §3.2, proof of Corollary 3.5, p. 485 (upper semicontinuity of `∂g*`): if
`y* ∈ int (dom g*)` and `∂g*(y*) ⊂ U` with `U` open, then `y*` has a neighbourhood
`V ⊂ int (dom g*)` with `∂g*(V) ⊂ U`, and more precisely `∂g*(V) ⊂ U ∩ dom g`. -/
theorem exists_nhds_subdiff_conj_subset {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal)
    (hgh : TaoAnDCA.GlobalOpt.DCStanding g h) (ys : EuclideanSpace ℝ (Fin n)) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (h12a : ys ∈ interior (TaoAnDCA.GlobalOpt.effDom (CondatPD.FinDim.conj g)))
    (h12b : TaoAnDCA.GlobalOpt.subdiff (CondatPD.FinDim.conj g) ys ⊆ U) :
    ∃ V ∈ 𝓝 ys, V ⊆ interior (TaoAnDCA.GlobalOpt.effDom (CondatPD.FinDim.conj g)) ∧
      ∀ y ∈ V, TaoAnDCA.GlobalOpt.subdiff (CondatPD.FinDim.conj g) y ⊆ U ∩ TaoAnDCA.GlobalOpt.effDom g := by sorry

end TaoAnDCA.LocalOpt
