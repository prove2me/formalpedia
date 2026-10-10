-- Prove2me | Theorems.Thm_StochGradTrack_Const_theorem_1
-- name    : StochGradTrack.Const.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:44:46.466553+00:00
-- url     : https://prove2.me/theorems/aa4faa8a-e761-4218-b119-a2aa4d58b028
-- title:
--   Theorem 1, p. 416 — under (7), ρ(A) < 1 and the limsup bounds (8) on E‖x̄_k − x*‖² and (9) on E‖x_k − 1x̄_k‖²
-- statement:
--   Assume Assumptions 1–4 and let $x^*$ minimize $f=\frac1n\sum_if_i$. Fix $\Gamma>1$ and run DSGT (4) from a deterministic $\mathbf x_0$ with a constant stepsize $\alpha>0$ satisfying
--   $$\alpha\le\min\left\{\frac{1-\rho_w^2}{12\rho_wL},\ \frac{(1-\rho_w^2)^2}{2\sqrt\Gamma\,L\max\{6\rho_w\|\mathbf W-\mathbf I\|,\,1-\rho_w^2\}},\ \frac{1-\rho_w^2}{3\rho_w^{2/3}L}\left[\frac{\mu^2}{L^2}\frac{\Gamma-1}{\Gamma(\Gamma+1)}\right]^{1/3}\right\},\tag{7}$$
--   where $\rho_w>0$ is the spectral norm of $\mathbf W-\frac1n\mathbf 1\mathbf 1^\top$ and $\|\mathbf W-\mathbf I\|$ the Frobenius norm, and also $3\alpha L\le1$. Let $\beta=\frac{1-\rho_w^2}{2\rho_w^2}-4\alpha L-2\alpha^2L^2$ and
--   $$\mathbf A=\begin{bmatrix}1-\alpha\mu&\frac{\alpha L^2}{\mu n}(1+\alpha\mu)&0\\0&\frac12(1+\rho_w^2)&\alpha^2\frac{(1+\rho_w^2)\rho_w^2}{1-\rho_w^2}\\2\alpha nL^3&\left(\frac1\beta+2\right)\|\mathbf W-\mathbf I\|^2L^2+3\alpha L^3&\frac12(1+\rho_w^2)\end{bmatrix}.$$
--   Then $\rho(\mathbf A)<1$, $\|\bar x_k-x^*\|^2$ and $\|\mathbf x_k-\mathbf 1\bar x_k\|^2$ are integrable for every $k$, and, with $M_\sigma=[3\alpha^2L^2+2(\alpha L+1)(n+1)]\sigma^2$,
--   $$\limsup_{k\to\infty}\mathbb E\|\bar x_k-x^*\|^2\le\frac{\Gamma+1}{\Gamma}\frac{\alpha\sigma^2}{\mu n}+\frac{\Gamma+1}{\Gamma-1}\,\frac{4\alpha^2L^2(1+\alpha\mu)(1+\rho_w^2)\rho_w^2}{\mu^2n(1-\rho_w^2)^3}\,M_\sigma,\tag{8}$$
--   $$\limsup_{k\to\infty}\mathbb E\|\mathbf x_k-\mathbf 1\bar x_k\|^2\le\frac{\Gamma+1}{\Gamma-1}\,\frac{4\alpha^2(1+\rho_w^2)\rho_w^2\,(2\alpha^2L^3\sigma^2+\mu M_\sigma)}{\mu(1-\rho_w^2)^3}.\tag{9}$$
--
--   The first term of (8) is the error of centralized stochastic gradient descent with $n$ samples per step and does not depend on the network; the network enters only through terms of order $\alpha^2$.
--
--   **Formalization Note.** Three hypotheses are added to the page's. (i) Assumptions 3–4 on $\mathbf W$: the page cites only Assumptions 1–2, but $\rho_w<1$ (Lemma 1) and the recursion need them. (ii) $\rho_w>0$: $\beta$, $\mathbf A$ and (7) divide by $\rho_w$. (iii) $3\alpha L\le1$: the proof of (20) needs it (see that item), and (7) does not imply it: its first term gives it only when $\rho_w\ge\sqrt5-2$, and for $\rho_w=0.01$, $\Gamma=1.1$, $\mu=L$ the bound (7) allows $\alpha\approx0.48/L$. "$\limsup_k a_k\le B$" is written as "for every $\varepsilon>0$, eventually $a_k\le B+\varepsilon$", which is equivalent for real sequences and has no junk value. Expectations are Bochner integrals, with integrability stated. The spectral radius is over $\mathbb C$. The theorem's other clause, that $\sup_{l\ge k}\mathbb E[\cdot]$ converges to the limsup at the rate $\mathcal O(\rho(\mathbf A)^k)$, has an unquantified constant and is not formalized: the paper's proof establishes only the envelope (22) and the limit $(\mathbf I-\mathbf A)^{-1}B$ of its right-hand side, not a rate of convergence of $\sup_{l\ge k}\mathbb E[\cdot]$ to the limsup (with noise laws that may change with $k$, such a rate need not hold); the envelope (22) is a milestone.
-- source:
--   Pu & Nedić, Math. Program. 187 (2021), Theorem 1 with (7)–(10), p. 416

import Mathlib
import Definitions.Def_StochGradTrack_Const_Model
import Definitions.Def_StochGradTrack_Const_Matrix

namespace StochGradTrack.Const

open MeasureTheory ProbabilityTheory Matrix

theorem theorem_1 {n p m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Fin n → E p → ℝ) (gradf : Fin n → E p → E p) (μ L : ℝ)
    (g : Fin n → E p → E m → E p) (ξ : ℕ → Fin n → Ω → E m) (σ : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (xstar : E p) (x0 : Stack n p)
    (hM : Model P f gradf μ L g ξ σ W xstar) (α : ℝ) (hα : 0 < α)
    (Γ : ℝ) (hΓ : 1 < Γ) (ρ w : ℝ) (hρdef : ρ = rhoW W) (hwdef : w = frobWI W) (hρ : 0 < ρ)
    (h7a : α ≤ (1 - ρ ^ 2) / (12 * ρ * L))
    (h7b : α ≤ (1 - ρ ^ 2) ^ 2 / (2 * Real.sqrt Γ * L * max (6 * ρ * w) (1 - ρ ^ 2)))
    (h7c : α ≤ (1 - ρ ^ 2) / (3 * ρ ^ (2 / 3 : ℝ) * L)
      * (μ ^ 2 / L ^ 2 * ((Γ - 1) / (Γ * (Γ + 1)))) ^ (1 / 3 : ℝ))
    (hαL : 3 * α * L ≤ 1) :
    spectralRadius ℂ ((Athm1 α μ L n ρ w).map (algebraMap ℝ ℂ)) < 1 ∧
    (∀ k, Integrable (fun ω => ‖avg (xs (fun _ => α) W g ξ x0 k ω) - xstar‖ ^ 2) P ∧
      Integrable (fun ω => consErr (xs (fun _ => α) W g ξ x0 k ω)) P) ∧
    (∀ ε > 0, ∀ᶠ k in Filter.atTop,
      ∫ ω, ‖avg (xs (fun _ => α) W g ξ x0 k ω) - xstar‖ ^ 2 ∂P
        ≤ (Γ + 1) / Γ * (α * σ ^ 2 / (μ * n))
          + (Γ + 1) / (Γ - 1) * (4 * α ^ 2 * L ^ 2 * (1 + α * μ) * (1 + ρ ^ 2) * ρ ^ 2
              / (μ ^ 2 * n * (1 - ρ ^ 2) ^ 3)) * Msigma α L n σ + ε) ∧
    (∀ ε > 0, ∀ᶠ k in Filter.atTop,
      ∫ ω, consErr (xs (fun _ => α) W g ξ x0 k ω) ∂P
        ≤ (Γ + 1) / (Γ - 1) * (4 * α ^ 2 * (1 + ρ ^ 2) * ρ ^ 2
            * (2 * α ^ 2 * L ^ 3 * σ ^ 2 + μ * Msigma α L n σ) / (μ * (1 - ρ ^ 2) ^ 3)) + ε)
    := by sorry

end StochGradTrack.Const
