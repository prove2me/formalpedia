-- Prove2me | Theorems.Thm_QAmpEst_Est_theorem_11_law
-- name    : QAmpEst.Est.theorem_11_law
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:56:31.017871+00:00
-- url     : https://prove2.me/theorems/629e0d7f-abc0-49de-bb02-428e11cea184
-- title:
--   Theorem 11, first part, p. 17 — Prob(X = Mω) = 1 if Mω ∈ ℤ; else Prob(X = x) = sin²(MΔπ)/(M² sin²(Δπ)) ≤ 1/(2MΔ)²
-- statement:
--   Let $M \ge 1$ and $0 \le \omega < 1$, and let $X$ be the result of measuring $F_M^{-1}|S_M(\omega)\rangle$ in the computational basis.
--
--   1. If $M\omega$ is an integer, then $\mathrm{Prob}(X = M\omega) = 1$.
--   2. Otherwise, for every $x \in \{0,\dots,M-1\}$, with $\Delta = d(\omega, x/M)$,
--   $$\mathrm{Prob}(X = x) = \frac{\sin^2(M\Delta\pi)}{M^2\sin^2(\Delta\pi)} \le \frac{1}{(2M\Delta)^2}.$$
--
--   This is the exact outcome law of Fourier-based phase estimation.
--
--   **Formalization Note** The first clause is stated as the existence of an outcome $x$ equal to $M\omega$ whose probability is $1$.
-- source:
--   arXiv:quant-ph/0005055v1, Theorem 11, p. 17

import Mathlib
import Definitions.Def_QAmpEst_Est_Fourier

open scoped Real

namespace QAmpEst.Est

/-- Theorem 11 (first part), arXiv:quant-ph/0005055v1, p. 17: let `X` be the outcome of
measuring `F_M⁻¹|S_M(ω)⟩` (`0 ≤ ω < 1`) in the computational basis. If `Mω` is an integer then
`Prob(X = Mω) = 1`. Otherwise, with `Δ = d(ω, x/M)`,
`Prob(X = x) = sin²(MΔπ) / (M² sin²(Δπ)) ≤ 1/(2MΔ)²`. -/
theorem theorem_11_law (M : ℕ) (hM : 0 < M) (ω : ℝ) (hω0 : 0 ≤ ω) (hω1 : ω < 1) :
    ((∃ n : ℤ, (M : ℝ) * ω = n) →
        ∃ x : Fin M, ((x : ℕ) : ℝ) = (M : ℝ) * ω ∧ phaseProb M ω x = 1) ∧
      ((¬ ∃ n : ℤ, (M : ℝ) * ω = n) → ∀ x : Fin M,
        let Δ := circDist ω (((x : ℕ) : ℝ) / (M : ℝ))
        phaseProb M ω x =
            Real.sin ((M : ℝ) * Δ * π) ^ 2 / ((M : ℝ) ^ 2 * Real.sin (Δ * π) ^ 2) ∧
          Real.sin ((M : ℝ) * Δ * π) ^ 2 / ((M : ℝ) ^ 2 * Real.sin (Δ * π) ^ 2) ≤
            1 / (2 * (M : ℝ) * Δ) ^ 2) := by sorry

end QAmpEst.Est
