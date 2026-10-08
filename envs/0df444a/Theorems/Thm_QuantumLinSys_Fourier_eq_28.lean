-- Prove2me | Theorems.Thm_QuantumLinSys_Fourier_eq_28
-- name    : QuantumLinSys.Fourier.eq_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:19:00.400407+00:00
-- url     : https://prove2.me/theorems/8aded09a-f11a-4bfd-99d7-a67d3a646d16
-- title:
--   (28), p. 11 — Gaussian tail bound
-- statement:
--   For every $z_K\ge0$, the upper tail of the standard Gaussian satisfies
--   $$
--   \frac1{\sqrt{2\pi}}\int_{z_K}^{\infty} e^{-z^2/2}\,dz
--   \le \frac12 e^{-z_K^2/2}.
--   $$
--
--   This is the tail estimate used in the truncation analysis of Lemma 12.
--
--   **Formalization Note** The nonnegative cutoff is the regime of the cited Gaussian-tail inequality; it is needed because the displayed bound is false for a negative cutoff. The Gaussian integrand is integrable.
-- source:
--   Childs, Kothari and Somma, Quantum algorithm for systems of linear equations with exponentially improved dependence on precision, arXiv:1511.02306v2, p. 11, display (28)

import Mathlib
import Definitions.Def_QuantumLinSys_Fourier_Setting

namespace QuantumLinSys.Fourier

/-- The one-sided Gaussian tail estimate (28), p. 11. -/
theorem eq_28 (zK : ℝ) (hz : 0 ≤ zK) :
    1 / Real.sqrt (2 * Real.pi) *
      ∫ z in Set.Ioi zK, Real.exp (-z ^ 2 / 2) ≤
        1 / 2 * Real.exp (-zK ^ 2 / 2) := by sorry

end QuantumLinSys.Fourier
