-- Prove2me | Theorems.Thm_StochKolmogorov_Persist_lemma_3_4
-- name    : StochKolmogorov.Persist.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:31:09.247598+00:00
-- url     : https://prove2.me/theorems/142e74e3-89af-416b-b128-702789cd6b63
-- title:
--   Lemma 3.4, p. 15 — if Π^{x_k}_{T_k} ⇒ π invariant, ‖x_k‖ ≤ M, T_k → ∞, then ∫h dΠ^{x_k}_{T_k} → ∫h dπ for h of growth (1+cᵀx)^δ(1+Σ(|fᵢ|+|gᵢ|²)), δ < δ₀
-- statement:
--   Throughout, $X$ is the solution of the stochastic Kolmogorov system $dX_i=X_if_i(X)\,dt+X_ig_i(X)\,dE_i$, $E=\Gamma^\top B$, $\Sigma=\Gamma^\top\Gamma=(\sigma_{ij})$, on $\mathbb R^n_+=[0,\infty)^n$ ($n\ge1$ populations), $\mathbb P_x,\mathbb E_x$ refer to the solution started at $x$, $\|x\|=\sum_i|x_i|$, and Assumption 1.1 (nondegenerate noise, locally Lipschitz coefficients, and the dissipativity condition (1.2) with $c\in\mathbb R^{n,\circ}_+$, $\gamma_b>0$) is in force. Fix $M>0$ as in (3.1) and $\delta_0$ as in (3.2), and write $\Pi^x_t(\cdot)=\frac1t\int_0^t\mathbb P_x\{X(s)\in\cdot\}ds$.
--
--   Suppose that
--
--   1. $(x_k)_{k\in\mathbb N}\subset\mathbb R^n_+$ and $(T_k)_{k\in\mathbb N}\subset\mathbb R_+$ satisfy $\|x_k\|\le M$, $T_k>1$ for all $k$, and $T_k\to\infty$;
--   2. $\Pi^{x_k}_{T_k}$ converges weakly to an invariant probability measure $\pi$;
--   3. $h:\mathbb R^n_+\to\mathbb R$ is continuous and $|h(x)|<K_h(1+c^\top x)^\delta\big(1+\sum_i(|f_i(x)|+|g_i(x)|^2)\big)$ on $\mathbb R^n_+$ for some $K_h\ge0$ and $\delta<\delta_0$.
--
--   Then $h$ is integrable with respect to every $\Pi^{x_k}_{T_k}$ and to $\pi$, and
--   $$\lim_{k\to\infty}\int_{\mathbb R^n_+}h(x)\,\Pi^{x_k}_{T_k}(dx)=\int_{\mathbb R^n_+}h(x)\,\pi(dx).$$
--
--   The lemma upgrades weak convergence of occupation measures to convergence of integrals of unbounded functions such as $\Phi$ of (4.3), the step that identifies the limit in Lemma 4.1.
--
--   **Formalization Note** Weak convergence is convergence of integrals of every bounded continuous function on $\mathbb R^n$ (equivalent, since all measures involved live on the closed set $\mathbb R^n_+$). Integrability of $h$ is part of the conclusion. The process is a family `X x` of strong solutions of (1.1), one from each $x\in\mathbb R^n_+$, driven by one standard Brownian motion on one probability space (`IsSolutionFamily`); by pathwise uniqueness (Lemma 3.1) nothing depends on that choice. Coordinates are indexed by `Fin n` (0-based). $n\ge1$ is a standing hypothesis.
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, Lemma 3.4, p. 15, with Π^x_t defined on p. 14

import Mathlib
import Definitions.Def_StochKolmogorov_Persist_Model
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Persist

open EthierKurtz

/-- Lemma 3.4 (p. 15): if `‖x_k‖ ≤ M`, `T_k > 1`, `T_k → ∞` and `Π^{x_k}_{T_k}` converges weakly to an
invariant probability measure `π`, then `∫ h dΠ^{x_k}_{T_k} → ∫ h dπ` for every continuous `h` with
`|h(x)| < K_h(1 + cᵀx)^δ(1 + ∑ᵢ(|fᵢ(x)| + |gᵢ(x)|²))`, `K_h ≥ 0`, `δ < δ₀`. -/
theorem lemma_3_4 {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (M : ℝ) (hMpos : 0 < M) (hM : IsRadiusM C c γb M) (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀)
    (xs : ℕ → SDEState n) (hxs : ∀ k, xs k ∈ orthant n ∧ l1 (xs k) ≤ M)
    (Ts : ℕ → ℝ) (hTs : ∀ k, 1 < Ts k) (hTs_lim : Tendsto Ts atTop atTop)
    (π : Measure (SDEState n)) (hπ : IsInvariant P X π)
    (hweak : ∀ h : SDEState n →ᵇ ℝ,
      Tendsto (fun k => ∫ y, h y ∂(occMean P X (xs k) (Ts k))) atTop (𝓝 (∫ y, h y ∂π)))
    (h : SDEState n → ℝ) (hcont : ContinuousOn h (orthant n)) (Kh δ : ℝ) (hKh : 0 ≤ Kh)
    (hδ : δ < δ₀)
    (hgrowth : ∀ x ∈ orthant n, |h x| <
      Kh * (1 + ∑ i, c i * x i) ^ δ * (1 + ∑ i, (|C.f i x| + |C.g i x| ^ 2))) :
    (∀ k, Integrable h (occMean P X (xs k) (Ts k))) ∧ Integrable h π ∧
      Tendsto (fun k => ∫ y, h y ∂(occMean P X (xs k) (Ts k))) atTop (𝓝 (∫ y, h y ∂π)) := by sorry

end StochKolmogorov.Persist
