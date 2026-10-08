-- Prove2me | Theorems.Thm_RobustRegLasso_WorstCaseExp_appendix_d_robust_identity
-- name    : RobustRegLasso.WorstCaseExp.appendix_d_robust_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:19:05.6356+00:00
-- url     : https://prove2.me/theorems/5fe79de6-eb68-4593-819e-14594e1c1d19
-- title:
--   Appendix D, first display — the worst case of $\|b+\sigma-(A+\Delta)x\|_2$ over admissible $(\sigma,\Delta)$ is attained and equals $\|b-Ax\|_2+\sqrt n c\|x\|_1+\sqrt n c$
-- statement:
--   Let $n\ge1$ and $m$ be integers, $b\in\mathbb R^n$, $A\in\mathbb R^{n\times m}$, $c\ge0$ and $x\in\mathbb R^m$. Call $(\sigma,\Delta)$, with $\sigma\in\mathbb R^n$ and $\Delta=[\delta_1,\dots,\delta_m]\in\mathbb R^{n\times m}$, admissible if $\|\sigma\|_2\le\sqrt n\,c$ and $\|\delta_j\|_2\le\sqrt n\,c$ for every column $j$. Then
--   $$\max_{\|\sigma\|_2\le\sqrt n c;\ \forall j:\ \|\delta_j\|_2\le\sqrt n c}\ \big\|b+\sigma-(A+[\delta_1,\dots,\delta_m])x\big\|_2=\|b-Ax\|_2+\sqrt n\,c\,\|x\|_1+\sqrt n\,c ,$$
--   and the maximum is attained: the right-hand side is an upper bound for every admissible $(\sigma,\Delta)$ and is reached by one of them.
--
--   This is the robust-regression identity of the paper's first section applied to the augmented matrix $[A,\,b]$, in which the response is perturbed together with the features. It identifies the left-hand side of Corollary 3 with a worst-case residual.
--
--   **Formalization Note** The paper writes "max"; the statement is `IsGreatest` of the set of residual norms over admissible $(\sigma,\Delta)$, which asserts both the bound and its attainment. The hypotheses $n\ge1$ and $c\ge0$ are the paper's setting ($n$ samples, a nonnegative budget); they are left implicit on the page. $\Delta$ is indexed by rows (samples) and columns (features), and the norm constraint is on the columns.
-- source:
--   Xu, Caramanis, Mannor, Robust Regression and Lasso, arXiv:0811.1790v1, p. 22, Appendix D, proof of Corollary 3, first display

import Mathlib
import Definitions.Def_RobustRegLasso_WorstCaseExp_Basic

namespace RobustRegLasso.WorstCaseExp

/-- Appendix D, proof of Corollary 3, first display (arXiv:0811.1790v1, p. 22): for `n ≥ 1`,
`c ≥ 0` and every `x`,
`max_{‖σ‖₂ ≤ √n c; ∀j: ‖δⱼ‖₂ ≤ √n c} ‖b + σ − (A + [δ₁, …, δₘ])x‖₂ = ‖b − Ax‖₂ + √n c‖x‖₁ + √n c`,
with the maximum attained. -/
theorem appendix_d_robust_identity {n m : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin m) ℝ)
    (b : Fin n → ℝ) (c : ℝ) (hc : 0 ≤ c) (x : Fin m → ℝ) :
    IsGreatest
      {v : ℝ | ∃ (σ : Fin n → ℝ) (Δ : Matrix (Fin n) (Fin m) ℝ),
        Admissible c σ Δ ∧ v = l2norm (b + σ - Matrix.mulVec (A + Δ) x)}
      (regularizedLoss A b c x) := by sorry

end RobustRegLasso.WorstCaseExp
