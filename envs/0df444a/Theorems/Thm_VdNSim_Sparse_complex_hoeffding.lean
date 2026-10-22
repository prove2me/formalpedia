-- Prove2me | Theorems.Thm_VdNSim_Sparse_complex_hoeffding
-- name    : VdNSim.Sparse.complex_hoeffding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:31:54.033176+00:00
-- url     : https://prove2.me/theorems/586861c2-e601-4772-9627-ea5fb6d33f3c
-- title:
--   Appendix A, p. 23 — complex sample-mean concentration
-- statement:
--   Let $p$ be a probability law on a finite set $X$, and let $f:X\to\mathbb C$ satisfy $|f(x)|\le1$ for every $x$. For $K\ge1$ independent draws from $p$ and $\varepsilon>0$,
--
--   $$\Pr\left\{\left|\frac1K\sum_{k=1}^{K}f(x_k)-\sum_{x\in X}p_xf(x)\right|>\varepsilon\right\}\le4e^{-K\varepsilon^2/8}.$$
--
--   This form controls the complex functions $F_i$ and $G_i$ appearing in Theorem 3.
--
--   **Formalization Note** The paper states that a similar complex bound follows by splitting real and imaginary parts but does not print a constant. The displayed constant is the consequence of its Eq. (18). The positive tolerance and sample count specify the valid domain.
-- source:
--   Van den Nest, Simulating quantum computers with probabilistic methods, arXiv:0911.1624v3, p. 23, paragraph following Eq. (18)

import Mathlib
import Definitions.Def_VdNSim_Sparse_Model

noncomputable section

namespace VdNSim.Sparse

/-- Appendix A, p. 23, the complex-valued consequence of Eq. (18). -/
theorem complex_hoeffding {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    {K : ℕ} (hK : 0 < K) {ε : ℝ} (hε : 0 < ε) :
    sampleProb p K (fun xs =>
      ε < ‖(K : ℂ)⁻¹ * ∑ k, f (xs k) - expect p f‖) ≤
      4 * Real.exp (-((K : ℝ) * ε ^ 2) / 8) := by sorry

end VdNSim.Sparse
