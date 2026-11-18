-- Prove2me | Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_projected_regression_expected_error
-- name    : PrivateAgnosticHalfspace.Gaussian.projected_regression_expected_error
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T05:14:57.002549+00:00
-- url     : https://prove2.me/theorems/ab35710c-720d-4bc9-8f0b-5f9aa1f06fb7
-- title:
--   Expected error of projected Gaussian-smoothed regression
-- statement:
--   Let $a_1,\ldots,a_n\in\mathbb R^D$ and $y_1,\ldots,y_n\in\mathbb R$, with $n\ge1$, $\|a_i\|\le T$ and $|y_i|\le Y$, where $T>0$. Define $F(v)=n^{-1}\sum_i|\langle v,a_i\rangle-y_i|$. Fix a smoothing radius $r>0$, Gaussian noise scale $\tau\in\mathbb R$, and $\sigma>0$ satisfying
--
--   $$2T^2/n+2\tau^2D\le\sigma^2.$$
--
--   Run the projected accelerated stochastic method from zero on the Euclidean unit ball for $n$ steps, with $L=2T/r$, $\beta=\min\{(2L)^{-1},(\sigma n\sqrt n)^{-1}\}$, $\alpha_k=2/(k+1)$ and $\lambda_k=k\beta/2$. At each step use the independent oracle
--
--   $$G(v)=\frac1n\sum_i\operatorname{sign}(\langle v,a_i\rangle-y_i+r\|a_i\|Z_i)a_i+\tau W,$$
--
--   where the $Z_i$ are standard real Gaussians and $W$ is a standard Gaussian vector. All oracle records are independent and $\operatorname{sign}(0)=1$. If $V$ is the aggregated output, then for every $v_*\in\mathbb R^D$ with $\|v_*\|\le1$, the excess loss is integrable and
--
--   $$\mathbb E[F(V)-F(v_*)]\le rT+4L/n^2+5\sigma/\sqrt n.$$
--
--   This finite-record estimate supplies the optimization component of the private clipped-regression construction. The formal statement specifies the complete recurrence and independent Gaussian product law. It is a derived implementation lemma for the regression step, rather than a restatement of generic private convex ERM.
-- source:
--   Racca, Sanyal and Singhal, Privacy for Free in Efficient Agnostic Halfspace Learning, held STOC 2027 submission #1006, October 2026, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1006.pdf, §2.1 equation (4) and Appendix B Lemma B.4 (specialized regression implementation); accelerated recursion and summed estimate: Ghadimi and Lan, https://arxiv.org/abs/1310.3787v1, p.22 equation (3.36). Derived smoothing-and-noise estimate for this implementation.

import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Regression
import Definitions.Def_NonconvexAG_StochComposite_RSAG
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open PrivateAgnosticHalfspace.Gaussian
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

theorem PrivateAgnosticHalfspace.Gaussian.projected_regression_expected_error {D n : ℕ} (hn : 0 < n) (r τ T Y σ : ℝ)
    (hr : 0 < r) (hT : 0 < T) (hσ : 0 < σ)
    (a : Fin n → Vec D) (y : Fin n → ℝ) (ha : ∀ i, ‖a i‖ ≤ T) (hy : ∀ i, |y i| ≤ Y)
    (hσbound : 2*T^2/(n : ℝ)+2*τ^2*D ≤ σ^2) (vstar : Vec D) (hvstar : ‖vstar‖ ≤ 1) :
    let L := 2*T/r
    let β := min (1/(2*L)) (1/(σ*n*Real.sqrt n))
    let Ξ := (Fin n → ℝ) × Vec D
    let G := fun (v : Vec D) (q : Ξ) =>
      (n : ℝ)⁻¹ • (∑ i, (if 0 ≤ inner ℝ v (a i)-y i+r*‖a i‖*q.1 i then (1 : ℝ) else -1) • a i) + τ • q.2
    let out := NonconvexAG.StochComposite.xagSeq G
      (fun x z c => (max 1 ‖x-c • z‖)⁻¹ • (x-c • z))
      (fun k => 2/((k : ℝ)+1)) (fun _ => β) (fun k => (k : ℝ)*β/2) (fun _ => 1) 0
      (fun k (s : Fin (n+1) → Ξ) => if hk : k < n+1 then s ⟨k,hk⟩ else (0,0)) n
    let ν := Measure.pi (fun _ : Fin (n+1) =>
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).prod (gaussian D))
    let F := fun v : Vec D => (n : ℝ)⁻¹ * ∑ i, |inner ℝ v (a i)-y i|
    Integrable (fun s => F (out s)-F vstar) ν ∧
      (∫ s, F (out s)-F vstar ∂ν) ≤ r*T+4*L/(n : ℝ)^2+5*σ/Real.sqrt n
 := by sorry
