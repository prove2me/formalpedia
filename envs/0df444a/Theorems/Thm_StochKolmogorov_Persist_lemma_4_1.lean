-- Prove2me | Theorems.Thm_StochKolmogorov_Persist_lemma_4_1
-- name    : StochKolmogorov.Persist.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:32:04.808823+00:00
-- url     : https://prove2.me/theorems/0c64895b-4790-465b-b65b-a4792abda953
-- title:
--   Lemma 4.1, p. 16 — there is T* > 0 with (1/T)∫₀ᵀ 𝔼ₓΦ(X(t))dt ≤ −ρ* for all T > T* and x ∈ ∂ℝⁿ₊, ‖x‖ ≤ M
-- statement:
--   Throughout, $X$ is the solution of the stochastic Kolmogorov system $dX_i=X_if_i(X)\,dt+X_ig_i(X)\,dE_i$, $E=\Gamma^\top B$, $\Sigma=\Gamma^\top\Gamma=(\sigma_{ij})$, on $\mathbb R^n_+=[0,\infty)^n$ ($n\ge1$ populations), $\mathbb P_x,\mathbb E_x$ refer to the solution started at $x$, $\|x\|=\sum_i|x_i|$, and Assumption 1.1 (nondegenerate noise, locally Lipschitz coefficients, and the dissipativity condition (1.2) with $c\in\mathbb R^{n,\circ}_+$, $\gamma_b>0$) is in force. Suppose Assumption 1.2 holds. Fix $M>0$ as in (3.1), $\delta_0$ as in (3.2), and let $p\in\mathbb R^{n,\circ}_+$ with $\|p\|=\delta_0$ and $\rho^*>0$ be as in (4.1): $\sum_ip_i\lambda_i(\mu)\ge2\rho^*$ for every $\mu\in\mathcal M$. Let
--   $$\Phi(x)=\frac{\sum_ic_ix_if_i(x)}{1+c^\top x}-\frac12\frac{\sum_{i,j}\sigma_{ij}c_ic_jx_ix_jg_i(x)g_j(x)}{(1+c^\top x)^2}-\sum_ip_i\Big(f_i(x)-\frac{\sigma_{ii}g_i^2(x)}{2}\Big).\tag{4.3}$$
--   Then there is $T^*>0$ such that for every $T>T^*$ and every $x\in\partial\mathbb R^n_+$ with $\|x\|\le M$,
--   $$\frac1T\int_0^T\mathbb E_x\Phi(X(t))\,dt\le-\rho^*.\tag{4.2}$$
--
--   Starting on the boundary, the time average of $\Phi$ (the drift of $\ln V$) is eventually uniformly negative; this is the quantitative form of "every boundary measure repels".
--
--   **Formalization Note** The left side of (4.2) is written as $\int\Phi\,d\Pi^x_T$, the integral of $\Phi$ against the mean occupation measure $\Pi^x_T=\frac1T\int_0^T\mathbb P_x\{X(t)\in\cdot\}dt$ (the identity used in (4.5)); integrability of $\Phi$ with respect to $\Pi^x_T$ is part of the conclusion, never a hypothesis. $T^*$ is chosen before $T$ and $x$. The process is a family `X x` of strong solutions of (1.1), one from each $x\in\mathbb R^n_+$, driven by one standard Brownian motion on one probability space (`IsSolutionFamily`); by pathwise uniqueness (Lemma 3.1) nothing depends on that choice. Coordinates are indexed by `Fin n` (0-based). $n\ge1$ is a standing hypothesis.
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, Lemma 4.1 and (4.3), p. 16

import Mathlib
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Persist_Persistence
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Persist

open EthierKurtz

/-- Lemma 4.1 (p. 16): there is `T* > 0` such that for every `T > T*` and every
`x ∈ ∂ℝⁿ₊` with `‖x‖ ≤ M`, `(1/T) ∫₀ᵀ 𝔼ₓΦ(X(t)) dt ≤ −ρ*` (4.2), written as the integral of `Φ`
against the mean occupation measure `Πˣ_T`. -/
theorem lemma_4_1 {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (h12 : Assumption12 P C X) (M : ℝ) (hMpos : 0 < M) (hM : IsRadiusM C c γb M)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) (p : SDEState n) (hp : p ∈ openOrthant n) (hpδ : l1 p = δ₀)
    (ρ : ℝ) (hρ : 0 < ρ) (h41 : IsWeightedInvasionMin P C X p ρ) :
    ∃ Tstar : ℝ, 0 < Tstar ∧ ∀ T : ℝ, Tstar < T → ∀ x ∈ bdry n, l1 x ≤ M →
      Integrable (Phi C c p) (occMean P X x T) ∧
        ∫ y, Phi C c p y ∂(occMean P X x T) ≤ -ρ := by sorry

end StochKolmogorov.Persist
