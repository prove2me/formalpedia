-- Prove2me | Theorems.Thm_StochKolmogorov_Persist_proposition_4_1
-- name    : StochKolmogorov.Persist.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:32:19.120645+00:00
-- url     : https://prove2.me/theorems/dc667e88-c35a-4b95-9026-00cec08f765a
-- title:
--   Proposition 4.1, p. 17 — there are θ ∈ (0, δ₀/2), K_θ > 0 with 𝔼ₓV^θ(X(T)) ≤ V^θ(x)exp(−½θρ*T) + K_θ for T ∈ [T*, n*T*], x ∈ ℝⁿ,◦₊, ‖x‖ ≤ M
-- statement:
--   Throughout, $X$ is the solution of the stochastic Kolmogorov system $dX_i=X_if_i(X)\,dt+X_ig_i(X)\,dE_i$, $E=\Gamma^\top B$, $\Sigma=\Gamma^\top\Gamma=(\sigma_{ij})$, on $\mathbb R^n_+=[0,\infty)^n$ ($n\ge1$ populations), $\mathbb P_x,\mathbb E_x$ refer to the solution started at $x$, $\|x\|=\sum_i|x_i|$, and Assumption 1.1 (nondegenerate noise, locally Lipschitz coefficients, and the dissipativity condition (1.2) with $c\in\mathbb R^{n,\circ}_+$, $\gamma_b>0$) is in force. Suppose Assumption 1.2 holds. Fix $M>0$ as in (3.1), $\delta_0$ as in (3.2), $H$ as in (3.5), and $p$, $\rho^*$ as in (4.1) with $\|p\|=\delta_0$; let $V(x)=(1+c^\top x)/\prod_ix_i^{p_i}$ (3.4). Let $T^*>0$ satisfy the conclusion of Lemma 4.1 (for every $T>T^*$ and $x\in\partial\mathbb R^n_+$ with $\|x\|\le M$, $\frac1T\int_0^T\mathbb E_x\Phi(X(t))dt\le-\rho^*$), and let $n^*\in\mathbb N$ satisfy
--   $$\gamma_b(n^*-1)>H.\tag{4.7}$$
--   Then there are $\theta\in(0,\delta_0/2)$ and $K_\theta>0$ such that for every $T\in[T^*,n^*T^*]$ and every $x\in\mathbb R^{n,\circ}_+$ with $\|x\|\le M$,
--   $$\mathbb E_xV^\theta(X(T))\le V^\theta(x)\exp\Big(-\frac12\theta\rho^*T\Big)+K_\theta .$$
--
--   Near the boundary, $V^\theta$ contracts by the factor $e^{-\theta\rho^*T/2}$ over a time window of length $T\in[T^*,n^*T^*]$: the process is pushed away from $\partial\mathbb R^n_+$ exponentially fast.
--
--   **Formalization Note** $\theta$ and $K_\theta$ are chosen before $T$ and $x$. The expectation is a lower Lebesgue integral of the nonnegative $V^\theta$. Lemma 4.1's conclusion is the hypothesis on $T^*$, in the same occupation-measure form as in that milestone. The process is a family `X x` of strong solutions of (1.1), one from each $x\in\mathbb R^n_+$, driven by one standard Brownian motion on one probability space (`IsSolutionFamily`); by pathwise uniqueness (Lemma 3.1) nothing depends on that choice. Coordinates are indexed by `Fin n` (0-based). $n\ge1$ is a standing hypothesis.
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, Proposition 4.1 and (4.7), p. 17

import Mathlib
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Persist_Persistence
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Persist

open EthierKurtz

/-- Proposition 4.1 (p. 17): with `p, ρ*` as in (4.1), `T*` as in Lemma 4.1 and `n*` as in (4.7),
there are `θ ∈ (0, δ₀/2)` and `K_θ > 0` with
`𝔼ₓV^θ(X(T)) ≤ V^θ(x) exp(−½θρ*T) + K_θ` for all `T ∈ [T*, n*T*]` and `x ∈ ℝⁿ,◦₊`, `‖x‖ ≤ M`. -/
theorem proposition_4_1 {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (h12 : Assumption12 P C X) (M : ℝ) (hMpos : 0 < M) (hM : IsRadiusM C c γb M)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) (p : SDEState n) (hp : p ∈ openOrthant n) (hpδ : l1 p = δ₀)
    (ρ : ℝ) (hρ : 0 < ρ) (h41 : IsWeightedInvasionMin P C X p ρ)
    (Tstar : ℝ) (hTstar : 0 < Tstar)
    (hT : ∀ T : ℝ, Tstar < T → ∀ x ∈ bdry n, l1 x ≤ M →
      Integrable (Phi C c p) (occMean P X x T) ∧ ∫ y, Phi C c p y ∂(occMean P X x T) ≤ -ρ)
    (nstar : ℕ) (hnstar : Hconst C c γb δ₀ < γb * ((nstar : ℝ) - 1)) :
    ∃ θ : ℝ, 0 < θ ∧ θ < δ₀ / 2 ∧ ∃ Kθ : ℝ, 0 < Kθ ∧
      ∀ T : ℝ, Tstar ≤ T → T ≤ nstar * Tstar → ∀ x ∈ openOrthant n, l1 x ≤ M →
        ∫⁻ ω, ENNReal.ofReal (Vfun c p (X x T.toNNReal ω) ^ θ) ∂P ≤
          ENNReal.ofReal (Vfun c p x ^ θ * Real.exp (-(1 / 2) * θ * ρ * T) + Kθ) := by sorry

end StochKolmogorov.Persist
