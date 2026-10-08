-- Prove2me | Theorems.Thm_QuantumLinSys_Fourier_lemma_13
-- name    : QuantumLinSys.Fourier.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:19:10.988981+00:00
-- url     : https://prove2.me/theorems/c2d19350-55d4-4d5b-8b9e-9d93ba9b5187
-- title:
--   Lemma 13, p. 12 — Gaussian Poisson summation identity
-- statement:
--   Let $\omega\in\mathbb R$ and $\Delta_z>0$, and put $z_k=k\Delta_z$ for $k\in\mathbb Z$. Then
--   $$
--   \sum_{k\in\mathbb Z}e^{-(\omega+2\pi k/\Delta_z)^2/2}
--   =\frac1{\sqrt{2\pi}}\sum_{k\in\mathbb Z}
--     \Delta_z e^{-z_k^2/2}e^{-i\omega z_k}.
--   $$
--
--   This Gaussian form of Poisson summation relates the sampled Fourier kernel to its periodic Gaussian transform in the proof of Lemma 11.
--
--   **Formalization Note** Both integer-indexed series are summable Gaussians; Lean's total-sum convention therefore represents the ordinary convergent sums.
-- source:
--   Childs, Kothari and Somma, Quantum algorithm for systems of linear equations with exponentially improved dependence on precision, arXiv:1511.02306v2, p. 12, Lemma 13 and display (32)

import Mathlib
import Definitions.Def_QuantumLinSys_Fourier_Setting

namespace QuantumLinSys.Fourier

/-- The Gaussian Poisson summation identity (32), Lemma 13, p. 12. -/
theorem lemma_13 (ω Δz : ℝ) (hΔ : 0 < Δz) :
    (∑' k : ℤ, (Real.exp (-(ω + 2 * Real.pi * (k : ℝ) / Δz) ^ 2 / 2) : ℂ)) =
      1 / (Real.sqrt (2 * Real.pi) : ℂ) *
        ∑' k : ℤ, (Δz : ℂ) *
          (Real.exp (-((k : ℝ) * Δz) ^ 2 / 2) : ℂ) *
          Complex.exp (-Complex.I * ω * ((k : ℝ) * Δz)) := by sorry

end QuantumLinSys.Fourier
