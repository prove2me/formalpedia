-- Prove2me | Theorems.Thm_ProxADMMLC_Conv_cor_3_8
-- name    : ProxADMMLC.Conv.cor_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:48:02.320122+00:00
-- url     : https://prove2.me/theorems/1301cb6f-f05f-4535-bc68-2427030d59cd
-- title:
--   Corollary 3.8, p. 2281 — small ‖Ax(w, z) − b‖ for w ∈ ỹ⁰ + range(A) implies ‖x(w, z) − x*(z)‖ < ε
-- statement:
--   Suppose Assumption 2.2(a) and (c) hold, $\gamma$ satisfies (2.4), and $\Gamma>0$, $p>0$, $p>-\gamma$. Let $x(y,z)$ and $x^*(z)$ be the minimizers (2.7) and (2.9). Fix $\tilde y^0\in\mathbb R^m$. For every $\varepsilon>0$ there is $\delta(\varepsilon)>0$ such that for every $z\in P$ and every $w\in\tilde y^0+\operatorname{range}(A)$,
--   $$\|Ax(w,z)-b\|<\delta(\varepsilon)\quad\Longrightarrow\quad\|x(w,z)-x^*(z)\|<\varepsilon.$$
--
--   A small dual residual of the augmented subproblem forces its solution close to the solution of the proximal problem (2.8); the proof of Theorem 2.4 uses it in Case 1 of the analysis of (3.37).
--
--   **Formalization Note** The page states the corollary for $y^+$ with $y\in\tilde y^0+\operatorname{range}(A)$, where $x$ is not in scope. Every such $y^+=y+\alpha(Ax-b)$ again lies in $\tilde y^0+\operatorname{range}(A)$, because $b\in\operatorname{range}(A)$ by Assumption 2.2(a); the statement here quantifies over all $w$ in that affine set, which covers every $y^+$ and is what Appendix B proves.
-- source:
--   Zhang & Luo, A proximal alternating direction method of multiplier for linearly constrained nonconvex minimization, SIAM J. Optim. 30(3) (2020), p. 2281, Corollary 3.8 (proof in Appendix B, p. 2300)

import Mathlib
import Definitions.Def_ProxADMMLC_Conv_Setting

namespace ProxADMMLC.Conv

theorem cor_3_8 {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ)
    (hℓu : ∀ i, ℓ i < u i) (ha : Assump22a A b ℓ u) (L : ℝ) (hf : Assump22c f ℓ u L)
    (γ : ℝ) (hγ : MonoConst f ℓ u γ) (Γ p : ℝ) (hΓ : 0 < Γ) (hp : 0 < p) (hpγ : -γ < p)
    (xs : E m → E n → E n) (hxs : IsXSel f A b ℓ u Γ p xs)
    (xst : E n → E n) (hxst : IsXStarSel f A b ℓ u p xst) :
    ∀ y0 : E m, ∀ ε > 0, ∃ δ > 0, ∀ z ∈ box ℓ u, ∀ w : E m,
      w - y0 ∈ LinearMap.range (A : E n →ₗ[ℝ] E m) → ‖A (xs w z) - b‖ < δ → ‖xs w z - xst z‖ < ε := by sorry

end ProxADMMLC.Conv
