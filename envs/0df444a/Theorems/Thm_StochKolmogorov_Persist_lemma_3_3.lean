-- Prove2me | Theorems.Thm_StochKolmogorov_Persist_lemma_3_3
-- name    : StochKolmogorov.Persist.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:31:11.474087+00:00
-- url     : https://prove2.me/theorems/ac93fe95-4335-4d86-b7e5-e0eb69738f85
-- title:
--   Lemma 3.3, p. 14 — every invariant μ satisfies ∫(1+cᵀx)^{δ₀}(1+Σ(|fᵢ|+gᵢ²))dμ ≤ H₂, and the bracket of (1.2) has μ-mean zero
-- statement:
--   Throughout, $X$ is the solution of the stochastic Kolmogorov system $dX_i=X_if_i(X)\,dt+X_ig_i(X)\,dE_i$, $E=\Gamma^\top B$, $\Sigma=\Gamma^\top\Gamma=(\sigma_{ij})$, on $\mathbb R^n_+=[0,\infty)^n$ ($n\ge1$ populations), $\mathbb P_x,\mathbb E_x$ refer to the solution started at $x$, $\|x\|=\sum_i|x_i|$, and Assumption 1.1 (nondegenerate noise, locally Lipschitz coefficients, and the dissipativity condition (1.2) with $c\in\mathbb R^{n,\circ}_+$, $\gamma_b>0$) is in force. Fix $\delta_0$ as in (3.2) and let $H_2>0$ be any constant for which (3.8) of Lemma 3.2 holds for all $x\in\mathbb R^n_+$, $t>0$.
--
--   Let $\mu$ be an invariant probability measure of $X$. Then
--   $$\int_{\mathbb R^n_+}(1+c^\top x)^{\delta_0}\Big(1+\sum_i(|f_i(x)|+|g_i(x)|^2)\Big)\mu(dx)\le H_2,$$
--   the function $x\mapsto\frac{\sum_ic_ix_if_i(x)}{1+c^\top x}-\frac12\frac{\sum_{i,j}\sigma_{ij}c_ic_jx_ix_jg_i(x)g_j(x)}{(1+c^\top x)^2}$ is $\mu$-integrable, and
--   $$\int_{\mathbb R^n_+}\Big(\frac{\sum_ic_ix_if_i(x)}{1+c^\top x}-\frac12\frac{\sum_{i,j}\sigma_{ij}c_ic_jx_ix_jg_i(x)g_j(x)}{(1+c^\top x)^2}\Big)\mu(dx)=0.$$
--
--   The first bound makes the Lyapunov exponents $\lambda_i(\mu)$ well defined for every invariant $\mu$; the second identity is used to evaluate the limit in the proof of Lemma 4.1.
--
--   **Formalization Note** The first integral is a lower Lebesgue integral. Integrability of the bracket is part of the conclusion (it follows from the first bound), never a hypothesis. The process is a family `X x` of strong solutions of (1.1), one from each $x\in\mathbb R^n_+$, driven by one standard Brownian motion on one probability space (`IsSolutionFamily`); by pathwise uniqueness (Lemma 3.1) nothing depends on that choice. Coordinates are indexed by `Fin n` (0-based). $n\ge1$ is a standing hypothesis.
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, Lemma 3.3, p. 14

import Mathlib
import Definitions.Def_StochKolmogorov_Persist_Model
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Persist

open EthierKurtz

/-- Lemma 3.3 (p. 14): every invariant probability measure `μ` integrates the weight of (3.8)
with bound `H₂` (any `H₂` with (3.8)), and the bracket of (1.2) is `μ`-integrable with mean zero. -/
theorem lemma_3_3 {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) (H₂ : ℝ) (hH₂ : 0 < H₂)
    (h38 : ∀ x ∈ orthant n, ∀ t : ℝ≥0, 0 < t →
      ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) t,
          ENNReal.ofReal ((1 + ∑ i, c i * X x s.toNNReal ω i) ^ δ₀ *
            (1 + ∑ i, (|C.f i (X x s.toNNReal ω)| + |C.g i (X x s.toNNReal ω)| ^ 2)))) ∂P ≤
        ENNReal.ofReal (H₂ * ((1 + ∑ i, c i * x i) ^ δ₀ + t)))
    (μ : Measure (SDEState n)) (hμ : IsInvariant P X μ) :
    ∫⁻ x, ENNReal.ofReal ((1 + ∑ i, c i * x i) ^ δ₀ *
        (1 + ∑ i, (|C.f i x| + |C.g i x| ^ 2))) ∂μ ≤ ENNReal.ofReal H₂ ∧
      Integrable (cBracket C c) μ ∧ ∫ x, cBracket C c x ∂μ = 0 := by sorry

end StochKolmogorov.Persist
