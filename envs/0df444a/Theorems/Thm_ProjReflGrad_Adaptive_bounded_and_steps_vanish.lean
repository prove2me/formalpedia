-- Prove2me | Theorems.Thm_ProjReflGrad_Adaptive_bounded_and_steps_vanish
-- name    : ProjReflGrad.Adaptive.bounded_and_steps_vanish
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:15:35.208983+00:00
-- url     : https://prove2.me/theorems/e939f52e-aeb4-45ca-91e2-2547dcbccc84
-- title:
--   Proof of Theorem 4.4, p. 12 — the iterates are bounded and ‖x_{n+1} − y_n‖, ‖x_{n+1} − x_n‖ → 0
-- statement:
--   Assume (C1)–(C3): $H$ is a real Hilbert space, $C \subseteq H$ closed and convex, $F : H \to H$ monotone and $L$-Lipschitz with $L > 0$, and the solution set $S$ is nonempty. Let $\alpha \in (0, \sqrt2 - 1)$, $\lambda_{-1} > 0$, $\bar\lambda > 0$, and let $(x_n, y_n, \lambda_n, \tau_n)$ be a run of Algorithm 4.2. Then $(x_n)$ is bounded and
--   $$\lim_{n\to\infty}\|x_{n+1} - y_n\| = 0 \qquad\text{and}\qquad \lim_{n\to\infty}\|x_{n+1} - x_n\| = 0.$$
--
--   These are the conclusions the paper draws from (4.10) and Lemma 2.7, before identifying the weak limit.
-- source:
--   Malitsky, Projected Reflected Gradient Methods for Monotone Variational Inequalities, arXiv:1502.04968v1, p. 12, proof of Theorem 4.4

import Mathlib
import Definitions.Def_ProjReflGrad_Adaptive_Setting

namespace ProjReflGrad.Adaptive

/-- Proof of Theorem 4.4 (Malitsky 2015, p. 12): under (C1)–(C3) every run of Algorithm 4.2 has
`(x_n)` bounded, `‖x_{n+1} - y_n‖ → 0` and `‖x_{n+1} - x_n‖ → 0`. -/
theorem bounded_and_steps_vanish {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCcl : IsClosed C) (hCcv : Convex ℝ C) (F : H → H) (L : ℝ)
    (hC1 : (ProjReflGrad.Weak.solSet C F).Nonempty) (hC2 : ProjReflGrad.Weak.IsMonotoneMap F) (hL : 0 < L) (hC3 : ProjReflGrad.Weak.IsLipschitzMap F L)
    (α lamInit lamBar : ℝ) (hα0 : 0 < α) (hα1 : α < Real.sqrt 2 - 1) (hlamInit : 0 < lamInit)
    (hlamBar : 0 < lamBar) (x y : ℕ → H) (lam tau : ℕ → ℝ)
    (hrun : IsAdaptiveRun C F α lamInit lamBar x y lam tau) :
    Bornology.IsBounded (Set.range x) ∧
      Filter.Tendsto (fun n => ‖x (n + 1) - y n‖) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun n => ‖x (n + 1) - x n‖) Filter.atTop (nhds 0) := by sorry

end ProjReflGrad.Adaptive
