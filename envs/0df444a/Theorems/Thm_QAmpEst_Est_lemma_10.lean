-- Prove2me | Theorems.Thm_QAmpEst_Est_lemma_10
-- name    : QAmpEst.Est.lemma_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T22:56:19.779396+00:00
-- url     : https://prove2.me/theorems/5681f975-be6a-4983-b0f2-ca951877c6d2
-- title:
--   Lemma 10, p. 16 — |⟨S_M(ω₀)|S_M(ω₁)⟩|² = 1 if Δ = 0, else sin²(MΔπ)/(M² sin²(Δπ))
-- statement:
--   Let $M \ge 1$, let $0 \le \omega_0 < 1$ and $0 \le \omega_1 < 1$, and let $\Delta = d(\omega_0,\omega_1)$ be their circular distance. If $\Delta = 0$ then $|\langle S_M(\omega_0)|S_M(\omega_1)\rangle|^2 = 1$; otherwise
--   $$|\langle S_M(\omega_0)|S_M(\omega_1)\rangle|^2 = \frac{\sin^2(M\Delta\pi)}{M^2\sin^2(\Delta\pi)} .$$
--
--   The overlap of two phase states measures the distance between the phases they encode; this identity is the source of every probability estimate of Theorem 11.
-- source:
--   arXiv:quant-ph/0005055v1, Lemma 10, p. 16

import Mathlib
import Definitions.Def_QAmpEst_Est_Fourier

open scoped Real

namespace QAmpEst.Est

/-- Lemma 10, arXiv:quant-ph/0005055v1, p. 16: for `0 ≤ ω₀ < 1`, `0 ≤ ω₁ < 1` and
`Δ = d(ω₀, ω₁)`, `|⟨S_M(ω₀)|S_M(ω₁)⟩|² = 1` if `Δ = 0`, and otherwise
`|⟨S_M(ω₀)|S_M(ω₁)⟩|² = sin²(MΔπ) / (M² sin²(Δπ))`. -/
theorem lemma_10 (M : ℕ) (hM : 0 < M) (ω0 ω1 : ℝ) (hω0 : 0 ≤ ω0) (hω0' : ω0 < 1)
    (hω1 : 0 ≤ ω1) (hω1' : ω1 < 1) :
    let Δ := circDist ω0 ω1
    let ip := ∑ y, star (stateS M ω0 y) * stateS M ω1 y
    (Δ = 0 → Complex.normSq ip = 1) ∧
      (Δ ≠ 0 → Complex.normSq ip =
        Real.sin ((M : ℝ) * Δ * π) ^ 2 / ((M : ℝ) ^ 2 * Real.sin (Δ * π) ^ 2)) := by sorry

end QAmpEst.Est
