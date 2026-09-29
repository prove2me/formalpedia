-- Prove2me | Theorems.Thm_VectorSpaceOpt_gauss_markov_trace
-- name    : VectorSpaceOpt.gauss_markov_trace
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-23T21:27:20.460632+00:00
-- url     : https://prove2.me/theorems/3e141745-98eb-468d-bd9d-6569aea08904
-- title:
--   Gauss–Markov, deterministic form: componentwise minimality of KQKᵀ subject to KW = I
-- statement:
--   This is the deterministic problem to which the Gauss–Markov problem reduces once the randomness is integrated out.
--
--   Let $W$ be an $m \times n$ matrix with linearly independent columns and $Q$ an $m \times m$ **positive definite** matrix, and set
--
--   $$K_0 = (W^\top Q^{-1} W)^{-1} W^\top Q^{-1}.$$
--
--   Then three things hold.
--
--   1. $K_0 W = I$ — the constraint defining unbiasedness.
--   2. For every $n \times m$ matrix $K$ with $K W = I$, and every index $i$,
--   $$\big(K_0 Q K_0^\top\big)_{ii} \;\le\; \big(K Q K^\top\big)_{ii}.$$
--   3. $K_0 Q K_0^\top = (W^\top Q^{-1} W)^{-1}$.
--
--   The connection to estimation: an unbiased linear estimator $Ky$ of $\beta$ has error covariance $K Q K^\top$, so claim 2 says $K_0$ minimizes the variance of **every component** — a stronger statement than minimizing the trace, which it implies. The source obtains it by splitting the problem into $n$ separate constrained minimum norm problems, the $i$-th over the $i$-th row of $K$ in the inner product $\langle a, b\rangle_Q = a^\top Q b$, each solved by the dual approximation theorem of Mission I.
--
--   **Formalization Note.** The claim is purely matrix-algebraic — no probability space appears. The inequality compares corresponding diagonal entries and is not the Loewner order; nothing is asserted about off-diagonal entries.
-- source:
--   David G. Luenberger, Optimization by Vector Space Methods, John Wiley & Sons, 1969, §4.4, pp. 85–86 (the deterministic subproblem and its solution)

import Mathlib
open Matrix

namespace VectorSpaceOpt

theorem gauss_markov_trace {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ)
    (Q : Matrix (Fin m) (Fin m) ℝ) (hQ : Q.PosDef)
    (hW : LinearIndependent ℝ (fun j : Fin n => fun i : Fin m => W i j))
    (K₀ : Matrix (Fin n) (Fin m) ℝ) (hK₀ : K₀ = (Wᵀ * Q⁻¹ * W)⁻¹ * Wᵀ * Q⁻¹) :
    K₀ * W = 1 ∧
    (∀ K : Matrix (Fin n) (Fin m) ℝ, K * W = 1 →
      ∀ i, (K₀ * Q * K₀ᵀ) i i ≤ (K * Q * Kᵀ) i i) ∧
    K₀ * Q * K₀ᵀ = (Wᵀ * Q⁻¹ * W)⁻¹ := by sorry

end VectorSpaceOpt
