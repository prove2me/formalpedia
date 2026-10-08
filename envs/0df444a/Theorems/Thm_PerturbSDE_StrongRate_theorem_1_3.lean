-- Prove2me | Theorems.Thm_PerturbSDE_StrongRate_theorem_1_3
-- name    : PerturbSDE.StrongRate.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:11:39.023079+00:00
-- url     : https://prove2.me/theorems/4fe3188d-5481-4da6-b80b-60e2c29670da
-- title:
--   Theorem 1.3, p. 4 — the stopped-tamed Euler–Maruyama scheme (8) converges in L^r with strong rate 1/2 under (6), (7)
-- statement:
--   Let $d,m\in\mathbb N$, $T\in(0,\infty)$, and let $W$ be a standard $m$-dimensional $(\mathcal F_t)$-Brownian motion on a stochastic basis $(\Omega,\mathcal F,\mathbb P,(\mathcal F_t)_{t\in[0,T]})$. Let $c,r\in(0,\infty)$, $q_0,q_1\in(0,\infty]$, $\alpha\in[0,\infty)$ and $p,q\in[2,\infty)$ with $\frac1p+\frac1{q_0}+\frac1{q_1}=\frac1r$. Let $U_1\in C^1(\mathbb R^d,[0,\infty))$, $\mu\in C^1(\mathbb R^d,\mathbb R^d)$ and $\sigma\in C^1(\mathbb R^d,\mathbb R^{d\times m})$ have at most polynomially growing derivatives, and let $U_0\in C^3(\mathbb R^d,[1,\infty))$ satisfy, for all $x,y\in\mathbb R^d$ with $x\ne y$,
--   $$\sum_{i=1}^3\|U_0^{(i)}(x)\|\le c\,|U_0(x)|^{1-1/q},\qquad\|x\|^{1/c}\le c\,(1+U_0(x)),$$
--   $$\frac{\langle x-y,\mu(x)-\mu(y)\rangle+\frac{(p-1)(1+1/c)}2\|\sigma(x)-\sigma(y)\|^2_{HS}}{\|x-y\|^2}\le c+\frac{U_0(x)+U_0(y)}{2q_0Te^{\alpha T}}+\frac{U_1(x)+U_1(y)}{2q_1e^{\alpha T}},\tag{6}$$
--   $$(\mathcal G_{\mu,\sigma}U_0)(x)+\tfrac12\|\sigma(x)^*(\nabla U_0)(x)\|^2+U_1(x)\le\alpha U_0(x)+c.\tag{7}$$
--   Let $X$ be an adapted process with continuous sample paths solving $X_t=X_0+\int_0^t\mu(X_s)ds+\int_0^t\sigma(X_s)dW_s$ on $[0,T]$, with $\mathbb E[e^{U_0(X_0)}]<\infty$, and let $Z^N:\{0,\dots,N\}\times\Omega\to\mathbb R^d$, $N\in\mathbb N$, satisfy $Z^N_0=X_0$ and the stopped-tamed Euler–Maruyama recursion
--   $$Z^N_{n+1}=Z^N_n+\mathbb 1_{\{\|Z^N_n\|<\exp(|\ln(T/N)|^{1/2})\}}\,\frac{\mu(Z^N_n)\frac TN+\sigma(Z^N_n)(W_{(n+1)T/N}-W_{nT/N})}{1+\big\|\mu(Z^N_n)\frac TN+\sigma(Z^N_n)(W_{(n+1)T/N}-W_{nT/N})\big\|^2}.\tag{8}$$
--   Then there is a real number $C\in[0,\infty)$ such that for all $N\in\mathbb N$,
--   $$\sup_{n\in\{0,1,\dots,N\}}\|X_{nT/N}-Z^N_n\|_{L^r(\Omega;\mathbb R^d)}\le C\,N^{-1/2}.$$
--
--   This is the paper's headline result: an explicit, easily implementable scheme with strong convergence rate $\frac12$ for multidimensional SDEs whose coefficients are not globally monotone, covering for example the stochastic Lorenz equation with bounded noise, the stochastic van der Pol and Duffing–van der Pol oscillators.
--
--   **Formalization Note** "Assume the above setting" (p. 2) also introduces an Itô process $Y$ with coefficients $a,b$; they occur neither in the hypotheses (6)–(8) nor in the conclusion, are always satisfiable ($Y=X$), and are omitted. $X$ is the published `IsSolution` (continuous on $[0,T]$, adapted to the $\mathbb P$-completed filtration; normal filtration = right-continuity + completion; $W$ is a Brownian motion on $[0,\infty)$; for $H=\mathbb R^d$, $U=\mathbb R^m$ the cylindrical $I_U$-Wiener process is a standard Brownian motion). "Polynomially growing derivative" is $\|f'(x)\|\le\kappa(1+\|x\|^\kappa)$ for some $\kappa\ge0$. The exponential moment is a Lebesgue integral in $[0,\infty]$; $L^r$ norms are in $[0,\infty]$; $q_0,q_1=\infty$ are allowed, with $1/\infty=0$. $C$ is chosen before $N$; the supremum over $n$ is a bound for each $n\le N$; $Z^N$ is given for each $N\ge1$ and (8) is required for every $\omega$.
-- source:
--   Hutzenthaler, Jentzen, arXiv:1401.0295v1, p. 4, Theorem 1.3, (6)–(9)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_PerturbSDE_StrongRate_Setting
import Definitions.Def_PerturbSDE_StrongRate_Scheme

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace PerturbSDE.StrongRate

open EthierKurtz SabanisEuler.Shared

/-- Hutzenthaler–Jentzen, arXiv:1401.0295v1, p. 4, Theorem 1.3 (Strong convergence rates for
numerical approximations), (9): if `X` solves `dX = µ(X) dt + σ(X) dW` on `[0, T]`, the
coefficients are `C¹` with polynomially growing derivatives, `U_0 ∈ C³(ℝ^d, [1, ∞))` and
`U_1 ∈ C¹(ℝ^d, [0, ∞))` satisfy (6), (7), `𝔼[e^{U_0(X_0)}] < ∞`, and `Z^N` is the stopped-tamed
Euler–Maruyama scheme (8), then there is `C ∈ [0, ∞)` with
`sup_{n ∈ {0, …, N}} ‖X_{nT/N} − Z^N_n‖_{L^r} ≤ C N^{−1/2}` for all `N ∈ ℕ`. -/
theorem theorem_1_3 {d m : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 mΩ) [ℱ.IsRightContinuous]
    (T : ℝ≥0) (hT : 0 < T) (W : ℝ≥0 → Ω → SDEState m) (hW : IsWienerMartingale P ℱ W)
    (mu : SDEState d → SDEState d) (sigma : SDEState d → Diffusion d m)
    (X : ℝ≥0 → Ω → SDEState d)
    (hX : IsSolution P ℱ W T (X 0) (fun z => mu z.2) (fun z => sigma z.2) X)
    (c r : ℝ) (hc : 0 < c) (hr : 0 < r) (q₀ q₁ : ℝ≥0∞) (hq₀ : q₀ ≠ 0) (hq₁ : q₁ ≠ 0)
    (α : ℝ) (hα : 0 ≤ α) (p q : ℝ) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hexp : (ENNReal.ofReal p)⁻¹ + q₀⁻¹ + q₁⁻¹ = (ENNReal.ofReal r)⁻¹)
    (U₀ U₁ : SDEState d → ℝ)
    (hU₁ : ContDiff ℝ 1 U₁ ∧ (∀ x, 0 ≤ U₁ x) ∧
      ∃ κ : ℝ, 0 ≤ κ ∧ ∀ x, ‖fderiv ℝ U₁ x‖ ≤ κ * (1 + ‖x‖ ^ κ))
    (hmu : ContDiff ℝ 1 mu ∧ ∃ κ : ℝ, 0 ≤ κ ∧ ∀ x, ‖fderiv ℝ mu x‖ ≤ κ * (1 + ‖x‖ ^ κ))
    (hsigma : ContDiff ℝ 1 sigma ∧
      ∃ κ : ℝ, 0 ≤ κ ∧ ∀ x, ‖fderiv ℝ sigma x‖ ≤ κ * (1 + ‖x‖ ^ κ))
    (hU₀ : ContDiff ℝ 3 U₀ ∧ ∀ x, 1 ≤ U₀ x)
    (hU₀deriv : ∀ x : SDEState d,
      ∑ i ∈ Finset.Icc 1 3, ‖iteratedFDeriv ℝ i U₀ x‖ ≤ c * U₀ x ^ (1 - 1 / q))
    (hgrowth : ∀ x : SDEState d, ‖x‖ ^ (1 / c) ≤ c * (1 + U₀ x))
    (hEexp : ∫⁻ ω, ENNReal.ofReal (Real.exp (U₀ (X 0 ω))) ∂P < ⊤)
    (h6 : ∀ x y : SDEState d, x ≠ y →
      (inner ℝ (x - y) (mu x - mu y) + (p - 1) * (1 + 1 / c) / 2 * ‖sigma x - sigma y‖ ^ 2) /
          ‖x - y‖ ^ 2 ≤
        c + (q₀⁻¹).toReal * (U₀ x + U₀ y) / (2 * T * Real.exp (α * T)) +
          (q₁⁻¹).toReal * (U₁ x + U₁ y) / (2 * Real.exp (α * T)))
    (h7 : ∀ x : SDEState d,
      generator mu sigma U₀ x + 1 / 2 * noiseSq sigma U₀ x + U₁ x ≤ α * U₀ x + c)
    (Z : ℕ → ℕ → Ω → SDEState d) (hZ : IsStoppedTamedEuler mu sigma W T (X 0) Z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ n ≤ N,
      eLpNorm (fun ω => X ((n : ℝ≥0) * T / N) ω - Z N n ω) (ENNReal.ofReal r) P ≤
        ENNReal.ofReal (C * (N : ℝ) ^ (-(1 / 2 : ℝ))) := by sorry

end PerturbSDE.StrongRate
