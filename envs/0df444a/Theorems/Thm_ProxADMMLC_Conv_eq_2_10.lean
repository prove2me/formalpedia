-- Prove2me | Theorems.Thm_ProxADMMLC_Conv_eq_2_10
-- name    : ProxADMMLC.Conv.eq_2_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:47:42.539656+00:00
-- url     : https://prove2.me/theorems/1283a24e-02bf-4f18-85a9-617e60431aad
-- title:
--   (2.10), p. 2277 — weak duality: K(x, z; y) ≥ d(y, z) for x ∈ P, and M(z) ≥ d(y, z)
-- statement:
--   Let $K$ be the proximal augmented Lagrangian (2.5), let $x(y,z)$ be a minimizer of $K(\cdot,z;y)$ over the box $P$ with value $d(y,z)$ (2.6)–(2.7), and let $x^*(z)$ be a minimizer of $f(x)+\frac p2\|x-z\|^2$ over $\{x\in P:Ax=b\}$ with value $M(z)$ (2.8)–(2.9). Then for all $y\in\mathbb R^m$ and $z\in\mathbb R^n$,
--   $$K(x,z;y)\ \ge\ d(y,z)\quad(x\in P),\qquad M(z)\ \ge\ d(y,z).$$
--
--   The two inequalities make each of the bracketed terms of the potential $\phi^t=(K-d)+(M-d)+M$ nonnegative, which is how the potential is bounded below in (3.5).
--
--   **Formalization Note** The page writes the first inequality for all $y,z$ without $x\in P$; since $d$ is a minimum over $P$, it holds for $x\in P$, and the hypothesis $x\in P$ is added (every use has $x=x^t\in P$). No assumption on $f$, $\Gamma$ or $p$ is needed beyond the existence of the two minimizers, which are given as selections.
-- source:
--   Zhang & Luo, A proximal alternating direction method of multiplier for linearly constrained nonconvex minimization, SIAM J. Optim. 30(3) (2020), p. 2277, (2.10)

import Mathlib
import Definitions.Def_ProxADMMLC_Conv_Setting

namespace ProxADMMLC.Conv

theorem eq_2_10 {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ)
    (Γ p : ℝ) (xs : E m → E n → E n) (hxs : IsXSel f A b ℓ u Γ p xs)
    (xst : E n → E n) (hxst : IsXStarSel f A b ℓ u p xst) :
    (∀ x ∈ box ℓ u, ∀ (y : E m) (z : E n), dval f A b Γ p xs y z ≤ K f A b Γ p x z y) ∧
      ∀ (y : E m) (z : E n), dval f A b Γ p xs y z ≤ Mval f p xst z := by sorry

end ProxADMMLC.Conv
