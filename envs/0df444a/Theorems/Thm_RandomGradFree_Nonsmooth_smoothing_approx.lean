-- Prove2me | Theorems.Thm_RandomGradFree_Nonsmooth_smoothing_approx
-- name    : RandomGradFree.Nonsmooth.smoothing_approx
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T07:32:28.467989+00:00
-- url     : https://prove2.me/theorems/f90f6f87-5407-4720-9145-15ca95c4a1d1
-- title:
--   Theorem 1 (18) — $|f_\mu(x)-f(x)| \le \mu L_0(f)\, n^{1/2}$ for Lipschitz $f$
-- statement:
--   Let $E$ be a real inner product space of dimension $n$ and let $f : E \to \mathbb R$ be Lipschitz continuous with constant $L_0 \ge 0$, i.e. $|f(x) - f(y)| \le L_0\|x-y\|$ for all $x, y$. Let $\mu \ge 0$ and let $f_\mu(x) = \mathbb E_u f(x+\mu u)$ be the Gaussian smoothing of $f$. Then for every $x \in E$,
--
--   $$
--   |f_\mu(x) - f(x)| \le \mu L_0\, n^{1/2}.
--   $$
--
--   This quantifies how far the smoothed function is from the original one; in the random search method it bounds the gap between $f_\mu(x^*)$ and the optimal value $f^*$.
--
--   **Formalization Note** The paper writes $L_0(f)$ for the Lipschitz constant of $f \in C^{0,0}(E)$; here $L_0$ is any constant satisfying the Lipschitz inequality, which is what the bound needs (it is monotone in $L_0$).
-- source:
--   Nesterov, Spokoiny, Random Gradient-Free Minimization of Convex Functions, Found. Comput. Math. 17 (2017), p. 534, Theorem 1, Eq. (18)

import Mathlib
import Definitions.Def_RandomGradFree_Shared_smoothing

namespace RandomGradFree.Nonsmooth

theorem smoothing_approx {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (L₀ : ℝ) (hL₀ : 0 ≤ L₀) (hLip : ∀ x y, |f x - f y| ≤ L₀ * ‖x - y‖)
    (μ : ℝ) (hμ : 0 ≤ μ) (x : E) :
    |RandomGradFree.Shared.smoothing f μ x - f x| ≤ μ * L₀ * Real.sqrt (Module.finrank ℝ E) := by sorry

end RandomGradFree.Nonsmooth
