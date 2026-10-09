-- Prove2me | Theorems.Thm_RFRidge_Basic_theorem_1
-- name    : RFRidge.Basic.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:49:04.303655+00:00
-- url     : https://prove2.me/theorems/39f16a7e-6b41-44ef-abee-6ea77b1d4f2d
-- title:
--   Theorem 1, p. 6 — with λₙ = n^{-1/2} and Mₙ = c₀√n log(108κ²√n/δ) random features, E(f̂) − E(f_H) ≤ c₁log²(18/δ)/√n w.p. ≥ 1 − δ for n ≥ n₀
-- statement:
--   Let $X$ be a separable space and $(\Omega,\pi)$ a probability space, and let $K(x,x')=\int_\Omega\psi(x,\omega)\psi(x',\omega)\,d\pi(\omega)$ be a kernel with the integral representation (6), where $\psi$ is continuous with $|\psi(x,\omega)|\le\kappa$, $\kappa\in[1,\infty)$. Let $\rho$ be a probability measure on $X\times\mathbb R$ with $|y|\le b$ almost surely, $b>0$, and let $\mathcal E(f)=\int(f(x)-y)^2d\rho(x,y)$ be the expected risk. Let $\mathcal H$ be the reproducing kernel Hilbert space of $K$ and suppose $f_{\mathcal H}\in\mathcal H$ minimizes $\mathcal E$ over $\mathcal H$.
--
--   Then there are constants $c_0,c_1>0$, not depending on $n,\lambda,\delta$, and a threshold $n_0$ such that the following holds for every $\delta\in(0,1]$ and $n\ge n_0$. Draw $n$ samples $(x_i,y_i)$ i.i.d. from $\rho$ and, independently, $M_n$ features i.i.d. from $\pi$, where
--   $$\lambda_n=n^{-1/2},\qquad M_n=c_0\sqrt n\,\log\frac{108\kappa^2\sqrt n}{\delta},$$
--   and let $\widehat f_{\lambda_n,M_n}$ be the random-features ridge estimator (7). Then with probability at least $1-\delta$,
--   $$\mathcal E(\widehat f_{\lambda_n,M_n})-\mathcal E(f_{\mathcal H})\le\frac{c_1\log^2\frac{18}{\delta}}{\sqrt n}.$$
--
--   So $O(\sqrt n\log n)$ random features suffice for the $O(1/\sqrt n)$ excess risk of exact kernel ridge regression with $\lambda=n^{-1/2}$.
--
--   **Formalization Note** The constants $c_0,c_1$ are existential, quantified after the data $\pi,\psi,\kappa,\rho,b,\mathcal H,f_{\mathcal H}$ and before $\delta$ and $n$: the paper prints them without values and its appendix values depend on $\kappa$, $b$, $\|f_{\mathcal H}\|$ and $\|L\|$. The threshold is a function $n_0(\delta)$ of $\delta$ and of the fixed data: the page says $n_0$ does not depend on $f_{\mathcal H},\rho$, but the appendix's own $n_0$ (p. 33) depends on $\|L\|$, hence on the marginal of $\rho$. $M_n$ is rounded up to a natural number; $n\ge1$ is added ($\lambda_n=n^{-1/2}$). "With probability at least $1-\delta$" is "the failure event has measure at most $\delta$" under the product of $\rho^{\otimes n}$ and $\pi^{\otimes M_n}$. The bound on $\psi$ holds everywhere (the page says "almost surely") and $\psi$ is jointly measurable (added; see the definition file). $\mathcal H$ is Mathlib's RKHS whose kernel, applied to $1\in\mathbb R$, is $K$.
-- source:
--   Rudi & Rosasco, arXiv:1602.04474v5, Theorem 1, p. 6; Eq. (6) p. 4, Eq. (7) p. 5, Eq. (8) p. 5

import Mathlib
import Definitions.Def_RFRidge_Basic_Model

namespace RFRidge.Basic

open MeasureTheory

/-- Theorem 1, p. 6. Under (6) with `ψ` continuous and `|ψ| ≤ κ`, `κ ≥ 1`, and `|y| ≤ b` a.s. with
`b > 0`, if `f_H` minimizes the risk over the RKHS `H` of `K`, there are constants `c₀, c₁ > 0` (depending on
the fixed data, not on `n, λ, δ`) and a threshold `n₀(δ)` such that for every `δ ∈ (0, 1]` and `n ≥ n₀(δ)`,
`n ≥ 1`: with `λₙ = n^{-1/2}` and `Mₙ = ⌈c₀ √n log(108 κ² √n / δ)⌉` features, the event
`E(f̂_{λₙ,Mₙ}) − E(f_H) > c₁ log²(18/δ)/√n` has probability at most `δ` under the joint law of the `n`
i.i.d. samples from `ρ` and the `Mₙ` i.i.d. features from `π`. -/
theorem theorem_1 {X W : Type*} [TopologicalSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X] [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W]
    (π : Measure W) [IsProbabilityMeasure π] (ψ : X → W → ℝ) (κ : ℝ)
    (ρ : Measure (X × ℝ)) [IsProbabilityMeasure ρ] (b : ℝ)
    (hA : Thm1Assumptions ψ κ ρ b)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [RKHS ℝ H X ℝ]
    (hK : ∀ x x', RKHS.kernel H x x' 1 = kernelOf π ψ x x')
    (fH : H) (hfH : ∀ g : H, risk ρ fH ≤ risk ρ g) :
    ∃ c0 c1 : ℝ, 0 < c0 ∧ 0 < c1 ∧ ∃ n0 : ℝ → ℕ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ n : ℕ, 1 ≤ n → n0 δ ≤ n →
        ((Measure.pi fun _ : Fin n => ρ).prod
            (Measure.pi fun _ : Fin ⌈c0 * Real.sqrt n * Real.log (108 * κ ^ 2 * Real.sqrt n / δ)⌉₊ =>
              π))
          {p | c1 * Real.log (18 / δ) ^ 2 / Real.sqrt n <
                risk ρ (rfEstimator ψ ((n : ℝ) ^ (-(1 / 2 : ℝ))) p.1 p.2) - risk ρ fH}
          ≤ ENNReal.ofReal δ := by sorry

end RFRidge.Basic
