-- Prove2me | Theorems.Thm_TaoAnDCA_GlobalOpt_epsSubdiff_subset_iff_eq8
-- name    : TaoAnDCA.GlobalOpt.epsSubdiff_subset_iff_eq8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:48:13.07433+00:00
-- url     : https://prove2.me/theorems/cece0b66-cd7d-4950-9af6-cf7fbf6e8956
-- title:
--   §3.1, proof of Theorem 3.1, (8), p. 484 — for x* ∈ dom h, ∂_εh(x*) ⊂ ∂_εg(x*) ∀ε > 0 is condition (8)
-- statement:
--   Let $g,h\in\Gamma_0(\mathbb R^n)$ satisfy the standing inclusions (3) and let $x^*\in\operatorname{dom}h$. Then $\partial_\varepsilon h(x^*)\subset\partial_\varepsilon g(x^*)$ for every $\varepsilon>0$ if and only if
--   $$\forall\varepsilon>0,\ \forall y\in Y:\quad \langle x^*,y\rangle+\varepsilon\ge h(x^*)+h^*(y)\ \Longrightarrow\ \langle x^*,y\rangle+\varepsilon\ge g(x^*)+g^*(y).\tag{8}$$
--
--   The equivalence unfolds the definition of the $\varepsilon$-subdifferential through the conjugate: for $x^*\in\operatorname{dom}\theta$, $y\in\partial_\varepsilon\theta(x^*)$ exactly when $\theta(x^*)+\theta^*(y)\le\langle x^*,y\rangle+\varepsilon$. It is the second step of the proof of Theorem 3.1(i).
--
--   **Formalization Note** The sums $h(x^*)+h^*(y)$ and $g(x^*)+g^*(y)$ are extended reals and may be $+\infty$; the left-hand sides $\langle x^*,y\rangle+\varepsilon$ are real. The variable $y$, free in the paper's (8), is quantified over all of $Y$. The standing assumptions are carried as hypotheses, though only $g,h\in\Gamma_0$ is needed here.
-- source:
--   Pham Dinh & Le Thi, A d.c. optimization algorithm for solving the trust-region subproblem, SIAM J. Optim. 8 (1998), p. 484, §3.1, proof of Theorem 3.1, display (8)

import Mathlib
import Definitions.Def_TaoAnDCA_GlobalOpt_Setting

open TaoAnDCA.GlobalOpt

namespace TaoAnDCA.GlobalOpt

theorem epsSubdiff_subset_iff_eq8 {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal)
    (hgh : DCStanding g h) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ effDom h) :
    (∀ ε : ℝ, 0 < ε → epsSubdiff h ε x ⊆ epsSubdiff g ε x) ↔
      ∀ ε : ℝ, 0 < ε → ∀ y : EuclideanSpace ℝ (Fin n),
        ((inner ℝ x y + ε : ℝ) : EReal) ≥ h x + CondatPD.FinDim.conj h y →
          ((inner ℝ x y + ε : ℝ) : EReal) ≥ g x + CondatPD.FinDim.conj g y := by sorry

end TaoAnDCA.GlobalOpt
