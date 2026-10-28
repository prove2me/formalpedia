-- Prove2me | Theorems.Thm_VdNSim_Sparse_eq_18
-- name    : VdNSim.Sparse.eq_18
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:31:59.900374+00:00
-- url     : https://prove2.me/theorems/2502ead9-778c-4f72-bad4-2c7a55563233
-- title:
--   Eq. (18), p. 23 — Chernoff–Hoeffding bound for the sample mean
-- statement:
--   Let $p$ be a probability law on a finite set $X$, and let $f:X\to[-1,1]$ be real valued. Draw $K\ge1$ independent samples $x_1,\ldots,x_K$ from $p$. For every $\varepsilon>0$,
--
--   $$\Pr\left\{\left|\frac1K\sum_{k=1}^{K}f(x_k)-\sum_{x\in X}p_x f(x)\right|\le\varepsilon\right\}\ge 1-2e^{-K\varepsilon^2/4}.$$
--
--   This is the concentration estimate invoked for the bounded summands of the simulation estimator.
--
--   **Formalization Note** The independent variables are realized as evaluations of one function on independent draws from a finite probability mass function. The assumption $\varepsilon>0$ rules out a negative tolerance, for which the displayed event is empty.
-- source:
--   Van den Nest, Simulating quantum computers with probabilistic methods, arXiv:0911.1624v3, p. 23, Eq. (18)

import Mathlib
import Definitions.Def_VdNSim_Sparse_Model

noncomputable section

namespace VdNSim.Sparse

/-- Appendix A, Eq. (18), in the finite sampling model used by the paper. -/
theorem eq_18 {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (f : X → ℝ) (hf : ∀ x, f x ∈ Set.Icc (-1) 1)
    {K : ℕ} (hK : 0 < K) {ε : ℝ} (hε : 0 < ε) :
    1 - 2 * Real.exp (-((K : ℝ) * ε ^ 2) / 4) ≤
      sampleProb p K (fun xs =>
        |(K : ℝ)⁻¹ * ∑ k, f (xs k) - ∑ x, p x * f x| ≤ ε) := by sorry

end VdNSim.Sparse
