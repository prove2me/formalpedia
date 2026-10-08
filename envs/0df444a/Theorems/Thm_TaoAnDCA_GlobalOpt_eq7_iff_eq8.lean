-- Prove2me | Theorems.Thm_TaoAnDCA_GlobalOpt_eq7_iff_eq8
-- name    : TaoAnDCA.GlobalOpt.eq7_iff_eq8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:47:24.974982+00:00
-- url     : https://prove2.me/theorems/d49d0120-954d-4291-be5e-9f302d62f389
-- title:
--   §3.1, proof of Theorem 3.1, p. 484 — for x* ∈ dom h, (x* ∈ dom g and (7)) is equivalent to (8)
-- statement:
--   Let $g,h\in\Gamma_0(\mathbb R^n)$ satisfy the standing inclusions (3) and let $x^*\in\operatorname{dom}h$. Then the following are equivalent:
--
--   1. $x^*\in\operatorname{dom}g$ and
--   $$g(x^*)+g^*(y)\le h(x^*)+h^*(y)\qquad\forall y\in\operatorname{dom}h^*;\tag{7}$$
--   2. for every $\varepsilon>0$ and every $y\in Y$,
--   $$\langle x^*,y\rangle+\varepsilon\ge h(x^*)+h^*(y)\ \Longrightarrow\ \langle x^*,y\rangle+\varepsilon\ge g(x^*)+g^*(y).\tag{8}$$
--
--   The paper calls this equivalence easy to see; combined with the two previous steps it proves Theorem 3.1(i).
--
--   **Formalization Note** Sums are extended reals. The clause $x^*\in\operatorname{dom}g$ accompanies (7) as in the paper's "$x^*\in\mathcal P$ if and only if $x^*\in\operatorname{dom}g$ and (6)". When $x^*\in\operatorname{dom}h\setminus\operatorname{dom}g$ both sides are false: the first by the domain clause, the second because $\partial_\varepsilon h(x^*)$ is nonempty for $\varepsilon>0$ while $g(x^*)+g^*(y)=+\infty$.
-- source:
--   Pham Dinh & Le Thi, A d.c. optimization algorithm for solving the trust-region subproblem, SIAM J. Optim. 8 (1998), p. 484, §3.1, proof of Theorem 3.1: "It is easy to see the equivalence between (7) and (8)"

import Mathlib
import Definitions.Def_TaoAnDCA_GlobalOpt_Setting

open TaoAnDCA.GlobalOpt

namespace TaoAnDCA.GlobalOpt

theorem eq7_iff_eq8 {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal)
    (hgh : DCStanding g h) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ effDom h) :
    (x ∈ effDom g ∧ ∀ y ∈ effDom (CondatPD.FinDim.conj h),
        g x + CondatPD.FinDim.conj g y ≤ h x + CondatPD.FinDim.conj h y) ↔
      ∀ ε : ℝ, 0 < ε → ∀ y : EuclideanSpace ℝ (Fin n),
        ((inner ℝ x y + ε : ℝ) : EReal) ≥ h x + CondatPD.FinDim.conj h y →
          ((inner ℝ x y + ε : ℝ) : EReal) ≥ g x + CondatPD.FinDim.conj g y := by sorry

end TaoAnDCA.GlobalOpt
