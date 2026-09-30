-- Prove2me | Theorems.Thm_TierneyMH_Peskun_variance_identity
-- name    : TierneyMH.Peskun.variance_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T12:38:13.400703+00:00
-- url     : https://prove2.me/theorems/2496ebce-a2da-4b17-b726-609a01efe810
-- title:
--   Variance of $\sum_{i=1}^n f(X_i)$ for a stationary reversible chain, stated through $\langle f, H^i f\rangle$
-- statement:
--   Let $\pi$ be a probability measure on a measurable space $E$, let $H$ be a Markov kernel reversible with respect to $\pi$, and let $f \in L^2_0(\pi)$. Let $X_0, X_1, \dots$ be the Markov chain with initial distribution $\pi$ and transition kernel $H$. Then for every $n \ge 1$,
--
--   $$
--   \frac{1}{n}\operatorname{Var}_H\Bigl(\sum_{i=1}^{n} f(X_i)\Bigr) \;=\; \langle f, f\rangle + 2\sum_{i=1}^{n} \frac{n-i}{n}\,\langle f, H^{i} f\rangle ,
--   $$
--
--   where $\langle f, H^i f\rangle = \int f(x)\int f(y)\,H^i(x,dy)\,\pi(dx)$.
--
--   The paper writes the right-hand side as $\int \bigl(1 + 2\sum_{i=1}^n \frac{n-i}{n} x^i\bigr)\, e_{f,H}(dx)$, where $e_{f,H}$ is the spectral measure of $f$ with $\langle f, H^i f\rangle = \int x^i\, e_{f,H}(dx)$; this is the finite-$n$ step from which the limit $\int \frac{1+x}{1-x}\,e_{f,H}(dx)$ is read off.
--
--   **Formalization Note** The right-hand side is stated through the moments $\langle f, H^i f\rangle$ instead of the spectral measure $e_{f,H}$ (Mathlib has no spectral measure of a self-adjoint operator); substituting the moments into the paper's integrand gives exactly this expression. The variance is Mathlib's real `variance` (the real part of the extended variance, finite here), and the weights $(n-i)/n$ are computed in $\mathbb R$.
-- source:
--   L. Tierney, A Note on Metropolis–Hastings Kernels for General State Spaces, Ann. Appl. Probab. 8(1) (1998) 1–9, DOI 10.1214/aoap/1027961031, p. 5, proof of Theorem 4 (displayed identity for (1/n) Var_H)

import Mathlib
import Definitions.Def_TierneyMH_Peskun_chainMeasure
import Definitions.Def_TierneyMH_Peskun_lagInner

open MeasureTheory ProbabilityTheory

namespace TierneyMH.Peskun

/-- **Proof of Theorem 4** (Tierney 1998, p. 5, the display), stated through `⟨f, Hⁱ f⟩`.
Let `H` be a reversible Markov kernel with invariant distribution `π`, let `f ∈ L²₀(π)`, and let
`X₀, X₁, …` be the Markov chain with initial distribution `π` and kernel `H`
(`chainMeasure π H`). For every `n ≥ 1`,
`(1/n) Var_H(∑_{i=1}^{n} f(X_i)) = ⟨f, f⟩ + 2 ∑_{i=1}^{n} ((n − i)/n) ⟨f, Hⁱ f⟩`.
The paper writes the right side as `∫ (1 + 2 ∑ ((n−i)/n) xⁱ) e_{f,H}(dx)` through the spectral
measure `e_{f,H}` with `⟨f, Hⁱ f⟩ = ∫ xⁱ e_{f,H}(dx)`; the moment form here is that right side
with the moments substituted (Mathlib has no spectral measure of a self-adjoint operator).
The weights are computed in `ℝ` (`((n : ℝ) − i) / n`), not with truncated `ℕ` subtraction. -/
theorem variance_identity {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π]
    (H : Kernel E E) [IsMarkovKernel H] (hH : Kernel.IsReversible H π)
    (f : E → ℝ) (hf_meas : Measurable f) (hf : MemLp f 2 π) (hf0 : ∫ x, f x ∂π = 0)
    (n : ℕ) (hn : 1 ≤ n) :
    variance (pathSum f n) (chainMeasure π H) / n =
      ∫ x, f x ^ 2 ∂π +
        2 * ∑ i ∈ Finset.Icc 1 n, (((n : ℝ) - i) / n) * lagInner π H f i := by sorry

end TierneyMH.Peskun
