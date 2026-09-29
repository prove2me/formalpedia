-- Prove2me | Theorems.Thm_PathFindingLP_Centering_split_newton_step
-- name    : PathFindingLP.Centering.split_newton_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T22:37:14.286422+00:00
-- url     : https://prove2.me/theorems/412af15a-adbe-4c06-981f-867eb58c394f
-- title:
--   Lemma 3 (Split Newton Step): $\delta_t(\vec x^{(new)},\vec w^{(new)})\le\frac{2}{1+r}\gamma\,\delta_t^2$
-- statement:
--   Let $A\in\mathbb R^{m\times n}$ have full column rank, let $b\in\mathbb R^m$, $c\in\mathbb R^n$, $t\in\mathbb R$ and $r\ge0$. Let $(x^{(old)},w^{(old)})$ be feasible: $x^{(old)}\in S^0$ and $w^{(old)}>0$. Write $h=\vec h_t(x^{(old)},w^{(old)})$ for the weighted Newton step, $S_{(old)}=\mathrm{diag}(s(x^{(old)}))$, $W_{(old)}=\mathrm{diag}(w^{(old)})$, $\gamma=\gamma(s(x^{(old)}),w^{(old)})$ for the slack sensitivity and $\delta_t=\delta_t(x^{(old)},w^{(old)})$ for the centrality. Take the split step
--   $$x^{(new)}=x^{(old)}-\frac{1}{1+r}\,h,\qquad w^{(new)}=w^{(old)}+\frac{r}{1+r}\,W_{(old)}S_{(old)}^{-1}A\,h.$$
--   If $\delta_t\le\dfrac{1}{8\gamma}$, then $(x^{(new)},w^{(new)})$ is feasible and
--   $$\delta_t\big(x^{(new)},w^{(new)}\big)\le\frac{2}{1+r}\cdot\gamma\cdot\delta_t^2.$$
--
--   The full Newton step on $x$ is split between $x$ and the weights $w$: a fraction $\frac1{1+r}$ moves the point and the rest is absorbed by re-weighting, and centrality still improves quadratically, by an extra factor $\frac{2}{1+r}$. This is the mechanism behind the centering step of Theorem 5, which uses $r=c_r$.
--
--   **Formalization Note** The page does not quantify $r$; it is taken as any real $r\ge0$ ($r=0$ is the ordinary Newton step). $\gamma(x^{(old)},w^{(old)})$ on the page means $\gamma(s(x^{(old)}),w^{(old)})$, since Definition 2 takes slacks. Feasibility of the new pair is stated as part of the conclusion, because the bound on $\delta_t(x^{(new)},w^{(new)})$ presupposes it. Full column rank of $A$ is assumed (the paper leaves it implicit) so that the inverted matrices are genuine inverses.
-- source:
--   Lee, Sidford, Path Finding Methods for Linear Programming, FOCS 2014, pp. 424–433, p. 428, §IV.B, Lemma 3 (Split Newton Step)

import Mathlib
import Definitions.Def_PathFindingLP_Centering_SlackSensitivity

open Matrix

namespace PathFindingLP.Centering

/-- Lemma 3 (Split Newton Step), §IV.B, p. 428: for feasible `(x_old, w_old)` and `r ≥ 0`, put
`x_new = x_old - (1/(1+r)) h_t(x_old, w_old)` and
`w_new = w_old + (r/(1+r)) W_old S_old⁻¹ A h_t(x_old, w_old)`. If
`δ_t(x_old, w_old) ≤ 1 / (8 γ(s(x_old), w_old))` then `(x_new, w_new)` is feasible and
`δ_t(x_new, w_new) ≤ (2/(1+r)) γ(s(x_old), w_old) δ_t(x_old, w_old)²`. -/
theorem split_newton_step {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hA : A.rank = n) (t r : ℝ) (hr : 0 ≤ r)
    (xOld : Fin n → ℝ) (wOld : Fin m → ℝ) (hfeas : IsFeasible A b xOld wOld)
    (hδ : centrality A b c t xOld wOld ≤
      1 / (8 * slackSensitivity A (slack A b xOld) wOld)) :
    let h := newtonStep A b c t xOld wOld
    let xNew := xOld - (1 / (1 + r)) • h
    let wNew := wOld + (r / (1 + r)) •
      ((diagonal wOld * diagonal (fun i => (slack A b xOld i)⁻¹) * A) *ᵥ h)
    IsFeasible A b xNew wNew ∧
      centrality A b c t xNew wNew ≤
        2 / (1 + r) * slackSensitivity A (slack A b xOld) wOld *
          centrality A b c t xOld wOld ^ 2 := by sorry

end PathFindingLP.Centering
