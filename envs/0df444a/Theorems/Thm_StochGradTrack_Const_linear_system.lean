-- Prove2me | Theorems.Thm_StochGradTrack_Const_linear_system
-- name    : StochGradTrack.Const.linear_system
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:44:34.339736+00:00
-- url     : https://prove2.me/theorems/8dac0a4a-983b-4eba-8c20-cd3085210d8c
-- title:
--   (21), pp. 420–421 — the expected errors satisfy e_{k+1} ≤ A e_k + (α²σ²/n, 0, M_σ) componentwise
-- statement:
--   Under the hypotheses of (20) — Assumptions 1–4, $x^*$ minimizing $f$, constant stepsize $0<\alpha<\frac2{\mu+L}$ with $3\alpha L\le1$ — and for any $\beta>0$, let
--   $$e_k=\big(\mathbb E\|\bar x_k-x^*\|^2,\ \mathbb E\|\mathbf x_k-\mathbf 1\bar x_k\|^2,\ \mathbb E\|\mathbf y_k-\mathbf 1\bar y_k\|^2\big)^\top .$$
--   Then the three integrands are integrable for every $k$, and for every $k\ge0$, componentwise,
--   $$e_{k+1}\le\mathbf A\,e_k+\begin{bmatrix}\alpha^2\sigma^2/n\\0\\M_\sigma\end{bmatrix},$$
--   where $\mathbf A=[a_{ij}]$ has $a_{11}=1-\alpha\mu$, $a_{12}=\frac{\alpha L^2}{\mu n}(1+\alpha\mu)$, $a_{13}=0$, $a_{21}=0$, $a_{22}=\frac12(1+\rho_w^2)$, $a_{23}=\alpha^2\frac{(1+\rho_w^2)\rho_w^2}{1-\rho_w^2}$, $a_{31}=2\alpha nL^3$, $a_{32}=(\frac1\beta+2)\|\mathbf W-\mathbf I\|^2L^2+3\alpha L^3$, $a_{33}=(1+4\alpha L+2\alpha^2L^2+\beta)\rho_w^2$.
--
--   The three error quantities of DSGT obey a linear system of inequalities; the analysis of the constant-stepsize method reduces to the spectral radius of $\mathbf A$.
--
--   **Formalization Note.** The hypothesis $3\alpha L\le1$ is inherited from (20) (see that item). $\mathbf A$ is `Agen` with the free $\beta$.
-- source:
--   Pu & Nedić, Math. Program. 187 (2021), §3.1, (21) and the entries of A, pp. 420–421

import Mathlib
import Definitions.Def_StochGradTrack_Const_Model
import Definitions.Def_StochGradTrack_Const_Matrix

namespace StochGradTrack.Const

open MeasureTheory ProbabilityTheory Matrix

theorem linear_system {n p m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Fin n → E p → ℝ) (gradf : Fin n → E p → E p) (μ L : ℝ)
    (g : Fin n → E p → E m → E p) (ξ : ℕ → Fin n → Ω → E m) (σ : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (xstar : E p) (x0 : Stack n p)
    (hM : Model P f gradf μ L g ξ σ W xstar) (α : ℝ) (hα : 0 < α) (hαμL : α < 2 / (μ + L))
    (hαL : 3 * α * L ≤ 1) (β : ℝ) (hβ : 0 < β) :
    (∀ k, Integrable (fun ω => ‖avg (xs (fun _ => α) W g ξ x0 k ω) - xstar‖ ^ 2) P ∧
        Integrable (fun ω => consErr (xs (fun _ => α) W g ξ x0 k ω)) P ∧ Integrable (fun ω => consErr (ys (fun _ => α) W g ξ x0 k ω)) P) ∧
      ∀ k i, errVec P (fun _ => α) W g ξ x0 xstar (k + 1) i
        ≤ (Agen α β μ L n (rhoW W) (frobWI W) *ᵥ errVec P (fun _ => α) W g ξ x0 xstar k) i
          + noiseVec α L n σ i := by sorry

end StochGradTrack.Const
