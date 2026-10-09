-- Prove2me | Theorems.Thm_StochKolmogorov_Persist_lemma_3_2
-- name    : StochKolmogorov.Persist.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:31:25.083603+00:00
-- url     : https://prove2.me/theorems/15eaca53-1155-49db-b125-f472477060cd
-- title:
--   Lemma 3.2, p. 14 — moment bounds (3.7), (3.8) with constants H₁, H₂ uniform in x and t, and the Feller property
-- statement:
--   Throughout, $X$ is the solution of the stochastic Kolmogorov system $dX_i=X_if_i(X)\,dt+X_ig_i(X)\,dE_i$, $E=\Gamma^\top B$, $\Sigma=\Gamma^\top\Gamma=(\sigma_{ij})$, on $\mathbb R^n_+=[0,\infty)^n$ ($n\ge1$ populations), $\mathbb P_x,\mathbb E_x$ refer to the solution started at $x$, $\|x\|=\sum_i|x_i|$, and Assumption 1.1 (nondegenerate noise, locally Lipschitz coefficients, and the dissipativity condition (1.2) with $c\in\mathbb R^{n,\circ}_+$, $\gamma_b>0$) is in force. Fix $\delta_0$ as in (3.2).
--
--   There are $H_1,H_2>0$ such that for every $x\in\mathbb R^n_+$ and $t>0$,
--   $$\mathbb E_x(1+c^\top X(t))^{\delta_0}\le H_1+(1+c^\top x)^{\delta_0}e^{-\delta_0\gamma_bt}\tag{3.7}$$
--   and
--   $$\mathbb E_x\int_0^t(1+c^\top X(s))^{\delta_0}\Big[1+\sum_i\big(|f_i(X(s))|+|g_i(X(s))|^2\big)\Big]ds\le H_2\big((1+c^\top x)^{\delta_0}+t\big).\tag{3.8}$$
--   Moreover $X$ is a Feller process on $\mathbb R^n_+$: for every $t\ge0$ and every bounded continuous $h$, the map $x\mapsto\mathbb E_xh(X(t))$ is continuous on $\mathbb R^n_+$.
--
--   These bounds give tightness of the occupation measures and integrability of $f_i,g_i^2$ under every invariant measure (Lemma 3.3).
--
--   **Formalization Note** $H_1,H_2$ are chosen before $x$ and $t$. Both expectations are lower Lebesgue integrals of nonnegative integrands, so no integrability hypothesis is needed. "Feller" is used in the sense of Remark 3.1 ($T_t$ maps $C_b(\mathbb R^n_+)$ into itself); test functions are bounded continuous functions on $\mathbb R^n$, which is equivalent because every bounded continuous function on the closed set $\mathbb R^n_+$ extends and the process stays in $\mathbb R^n_+$. The process is a family `X x` of strong solutions of (1.1), one from each $x\in\mathbb R^n_+$, driven by one standard Brownian motion on one probability space (`IsSolutionFamily`); by pathwise uniqueness (Lemma 3.1) nothing depends on that choice. Coordinates are indexed by `Fin n` (0-based). $n\ge1$ is a standing hypothesis.
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, Lemma 3.2, p. 14, and Remark 3.1, p. 14

import Mathlib
import Definitions.Def_StochKolmogorov_Persist_Model
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Persist

open EthierKurtz

/-- Lemma 3.2 (p. 14): the moment bounds (3.7), (3.8), with `H₁, H₂` independent of `x` and `t`,
and the Feller property in the sense of Remark 3.1. -/
theorem lemma_3_2 {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) :
    ∃ H₁ H₂ : ℝ, 0 < H₁ ∧ 0 < H₂ ∧
      (∀ x ∈ orthant n, ∀ t : ℝ≥0, 0 < t →
        ∫⁻ ω, ENNReal.ofReal ((1 + ∑ i, c i * X x t ω i) ^ δ₀) ∂P ≤
          ENNReal.ofReal (H₁ + (1 + ∑ i, c i * x i) ^ δ₀ * Real.exp (-δ₀ * γb * t))) ∧
      (∀ x ∈ orthant n, ∀ t : ℝ≥0, 0 < t →
        ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) t,
            ENNReal.ofReal ((1 + ∑ i, c i * X x s.toNNReal ω i) ^ δ₀ *
              (1 + ∑ i, (|C.f i (X x s.toNNReal ω)| + |C.g i (X x s.toNNReal ω)| ^ 2)))) ∂P ≤
          ENNReal.ofReal (H₂ * ((1 + ∑ i, c i * x i) ^ δ₀ + t))) ∧
      (∀ (t : ℝ≥0) (h : SDEState n →ᵇ ℝ),
        ContinuousOn (fun x => ∫ ω, h (X x t ω) ∂P) (orthant n)) := by sorry

end StochKolmogorov.Persist
