-- Prove2me | Theorems.Thm_StochKolmogorov_Persist_eq_4_18
-- name    : StochKolmogorov.Persist.eq_4_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:32:06.740998+00:00
-- url     : https://prove2.me/theorems/a4101326-001b-491a-989c-de642f101852
-- title:
--   (4.18), Theorem 4.1, p. 18 — there are κ ∈ (0, 1), K̃ > 0 with 𝔼ₓV^θ(X(n*T*)) ≤ κV^θ(x) + K̃ for all x ∈ ℝⁿ,◦₊
-- statement:
--   Throughout, $X$ is the solution of the stochastic Kolmogorov system $dX_i=X_if_i(X)\,dt+X_ig_i(X)\,dE_i$, $E=\Gamma^\top B$, $\Sigma=\Gamma^\top\Gamma=(\sigma_{ij})$, on $\mathbb R^n_+=[0,\infty)^n$ ($n\ge1$ populations), $\mathbb P_x,\mathbb E_x$ refer to the solution started at $x$, $\|x\|=\sum_i|x_i|$, and Assumption 1.1 (nondegenerate noise, locally Lipschitz coefficients, and the dissipativity condition (1.2) with $c\in\mathbb R^{n,\circ}_+$, $\gamma_b>0$) is in force. Suppose Assumption 1.2 holds, and let $M>0,\delta_0,H,p,\rho^*,V,T^*,n^*$ be as in Proposition 4.1. Let $\theta\in(0,\delta_0/2)$ and $K_\theta>0$ satisfy the conclusion of Proposition 4.1: $\mathbb E_xV^\theta(X(T))\le V^\theta(x)e^{-\theta\rho^*T/2}+K_\theta$ for all $T\in[T^*,n^*T^*]$ and $x\in\mathbb R^{n,\circ}_+$ with $\|x\|\le M$. Then there are $\kappa=\kappa(\theta,T^*)\in(0,1)$ and $\widetilde K=\widetilde K(\theta,T^*)>0$ such that
--   $$\mathbb E_xV^\theta(X(n^*T^*))\le\kappa V^\theta(x)+\widetilde K\qquad\text{for all }x\in\mathbb R^{n,\circ}_+.\tag{4.18}$$
--
--   This is a geometric drift (Foster–Lyapunov) condition for the skeleton chain $X(kn^*T^*)$ on the whole interior, the input of the Meyn–Tweedie criterion.
--
--   **Formalization Note** $\kappa$ and $\widetilde K$ are chosen before $x$. The expectation is a lower Lebesgue integral. The process is a family `X x` of strong solutions of (1.1), one from each $x\in\mathbb R^n_+$, driven by one standard Brownian motion on one probability space (`IsSolutionFamily`); by pathwise uniqueness (Lemma 3.1) nothing depends on that choice. Coordinates are indexed by `Fin n` (0-based). $n\ge1$ is a standing hypothesis.
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, Theorem 4.1, (4.18), p. 18

import Mathlib
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Persist_Persistence
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Persist

open EthierKurtz

/-- (4.18), Theorem 4.1 (p. 18): with `θ, K_θ` as in Proposition 4.1 and `n*` as in (4.7), there are
`κ ∈ (0, 1)` and `K̃ > 0` with `𝔼ₓV^θ(X(n*T*)) ≤ κV^θ(x) + K̃` for all `x ∈ ℝⁿ,◦₊`. -/
theorem eq_4_18 {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (h12 : Assumption12 P C X) (M : ℝ) (hMpos : 0 < M) (hM : IsRadiusM C c γb M)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) (p : SDEState n) (hp : p ∈ openOrthant n) (hpδ : l1 p = δ₀)
    (ρ : ℝ) (hρ : 0 < ρ) (h41 : IsWeightedInvasionMin P C X p ρ)
    (Tstar : ℝ) (hTstar : 0 < Tstar)
    (hT : ∀ T : ℝ, Tstar < T → ∀ x ∈ bdry n, l1 x ≤ M →
      Integrable (Phi C c p) (occMean P X x T) ∧ ∫ y, Phi C c p y ∂(occMean P X x T) ≤ -ρ)
    (nstar : ℕ) (hnstar : Hconst C c γb δ₀ < γb * ((nstar : ℝ) - 1))
    (θ : ℝ) (hθ : 0 < θ) (hθδ : θ < δ₀ / 2) (Kθ : ℝ) (hKθ : 0 < Kθ)
    (hprop : ∀ T : ℝ, Tstar ≤ T → T ≤ nstar * Tstar → ∀ x ∈ openOrthant n, l1 x ≤ M →
      ∫⁻ ω, ENNReal.ofReal (Vfun c p (X x T.toNNReal ω) ^ θ) ∂P ≤
        ENNReal.ofReal (Vfun c p x ^ θ * Real.exp (-(1 / 2) * θ * ρ * T) + Kθ)) :
    ∃ κ : ℝ, 0 < κ ∧ κ < 1 ∧ ∃ Kt : ℝ, 0 < Kt ∧ ∀ x ∈ openOrthant n,
      ∫⁻ ω, ENNReal.ofReal (Vfun c p (X x ((nstar : ℝ) * Tstar).toNNReal ω) ^ θ) ∂P ≤
        ENNReal.ofReal (κ * Vfun c p x ^ θ + Kt) := by sorry

end StochKolmogorov.Persist
