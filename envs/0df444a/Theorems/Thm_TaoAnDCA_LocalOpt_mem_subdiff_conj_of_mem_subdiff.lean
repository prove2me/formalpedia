-- Prove2me | Theorems.Thm_TaoAnDCA_LocalOpt_mem_subdiff_conj_of_mem_subdiff
-- name    : TaoAnDCA.LocalOpt.mem_subdiff_conj_of_mem_subdiff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:23:11.120802+00:00
-- url     : https://prove2.me/theorems/36485c19-9ddb-47b6-a4f0-eeb27a672dd5
-- title:
--   §3.2, proof of Corollary 3.5, p. 485 — y* ∈ ∂h(x*) ∩ ∂g(x*) gives x* ∈ ∂g*(y*) ∩ ∂h*(y*)
-- statement:
--   Let $g, h \in \Gamma_0(\mathbb R^n)$ satisfy the standing inclusions $\operatorname{dom} g \subset \operatorname{dom} h$ and $\operatorname{dom} h^* \subset \operatorname{dom} g^*$. If $y^* \in \partial h(x^*)$ and $y^* \in \partial g(x^*)$, then
--   $$x^* \in \partial g^*(y^*) \cap \partial h^*(y^*).$$
--
--   In the proof of Corollary 3.5 this inverts the subgradient relation: after Theorem 3.2(i) gives $y^* \in \partial h(x^*) \subset \partial g(x^*)$, the point $x^*$ is a common subgradient of the two dual components at $y^*$, i.e. $y^*$ is a critical point of $h^* - g^*$.
--
--   **Formalization Note.** Membership $x^* \in \partial g^*(y^*)$ uses the published `IsSubgradient`, which also asserts $g^*(y^*) < +\infty$; the conjugate is the `EReal` supremum `CondatPD.FinDim.conj`.
-- source:
--   Pham Dinh & Le Thi, A d.c. optimization algorithm for solving the trust-region subproblem, SIAM J. Optim. 8 (1998), p. 485, §3.2, proof of Corollary 3.5, second sentence

import Mathlib
import Definitions.Def_TaoAnDCA_LocalOpt_Setting

open Filter Topology

namespace TaoAnDCA.LocalOpt

/-- §3.2, proof of Corollary 3.5, p. 485: if `y* ∈ ∂h(x*)` and `y* ∈ ∂g(x*)`, then
`x* ∈ ∂g*(y*) ∩ ∂h*(y*)`. -/
theorem mem_subdiff_conj_of_mem_subdiff {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal)
    (hgh : TaoAnDCA.GlobalOpt.DCStanding g h) (xs ys : EuclideanSpace ℝ (Fin n))
    (hy : ys ∈ TaoAnDCA.GlobalOpt.subdiff h xs) (hyg : ys ∈ TaoAnDCA.GlobalOpt.subdiff g xs) :
    xs ∈ TaoAnDCA.GlobalOpt.subdiff (CondatPD.FinDim.conj g) ys ∩ TaoAnDCA.GlobalOpt.subdiff (CondatPD.FinDim.conj h) ys := by sorry

end TaoAnDCA.LocalOpt
