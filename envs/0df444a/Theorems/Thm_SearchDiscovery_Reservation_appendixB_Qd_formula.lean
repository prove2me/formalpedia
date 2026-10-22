-- Prove2me | Theorems.Thm_SearchDiscovery_Reservation_appendixB_Qd_formula
-- name    : SearchDiscovery.Reservation.appendixB_Qd_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:27:42.771189+00:00
-- url     : https://prove2.me/theorems/2b7032ed-54b7-4cab-aae5-3b6169457873
-- title:
--   Appendix B, p. 43 — Q_d(z) = E[max{z, max_k W̃_k}] − z − c_d = ∫_z^∞ (1 − H(w)) dw − c_d
-- statement:
--   Let $z^s$ be a search value function, $Q_s(x,c_s,z^s(x))=0$ for every $x$. Draw $n_d$ i.i.d. pairs $(X_k,Y_k)\sim G\otimes F_{Y\mid X}$ and set
--   $$\tilde W_k=\min\{z^s(X_k),\,X_k+Y_k\},\qquad k=1,\dots,n_d,$$
--   so that $\tilde W_k=X_k+\min\{Y_k,\xi_{X_k}\}$. Let $H$ be the cumulative distribution function of $\max_k\tilde W_k$. Then for every $z\in\mathbb R$,
--   $$Q_d(c_d,c_s,z)=\mathbb E_{\boldsymbol X,\boldsymbol Y}\Big[\max\Big\{z,\max_{k}\tilde W_k\Big\}\Big]-z-c_d=\mathbb E_{\boldsymbol X,\boldsymbol Y}\Big[\max\Big\{0,\max_{k}\tilde W_k-z\Big\}\Big]-c_d=\int_z^\infty\big(1-H(w)\big)\,\mathrm dw-c_d .$$
--
--   The first equality evaluates the optimal value of the reduced problem inside (9) (an outside option $z$ and the $n_d$ newly discovered products, no further discovery) in closed form; the last expresses $Q_d$ through the tail of $H$, from which the monotonicity and uniqueness of the discovery value follow.
--
--   **Formalization Note.** The maximum over $k$ is a supremum over the nonempty finite index set $\{1,\dots,n_d\}$; $H$ is the cdf of the image of the product law under $\max_k\tilde W_k$. $Q_d$ is defined from the optimal value of the reduced problem, not from this closed form.
-- source:
--   Greminger, Optimal Search and Discovery, arXiv:1911.07773v5, p. 43, Appendix B (display for Q_d); p. 18 and p. 38 for the definition of w̃

import Mathlib
import Definitions.Def_SearchDiscovery_Reservation_Model

namespace SearchDiscovery.Reservation

open MeasureTheory ProbabilityTheory

theorem appendixB_Qd_formula (M : SDModel) (hM : M.Standing)
    (zs : ℝ → ℝ) (hzs : ∀ x, M.Qs x (zs x) = 0) (z : ℝ) :
    let W : (Fin M.nd → ℝ × ℝ) → ℝ :=
      fun p => ⨆ k : Fin M.nd, min (zs (p k).1) ((p k).1 + (p k).2)
    let μ : Measure (Fin M.nd → ℝ × ℝ) := Measure.pi fun _ : Fin M.nd => M.G ⊗ₘ M.κ
    M.Qd z = (∫ p, max z (W p) ∂μ) - z - M.cd ∧
    M.Qd z = (∫ p, max 0 (W p - z) ∂μ) - M.cd ∧
    M.Qd z = (∫ w in Set.Ioi z, (1 - cdf (μ.map W) w)) - M.cd := by sorry

end SearchDiscovery.Reservation
