-- Prove2me | Theorems.Thm_Wigner_wigner_norm
-- name    : Wigner.wigner_norm
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-18T16:50:39.789733+00:00
-- url     : https://prove2.me/theorems/5f27eb6b-32b9-4c0b-876d-e69c597841d5
-- title:
--   Total integral of the Wigner function
-- statement:
--   The total integral of the Wigner function is the squared $L^2$ norm of the wavefunction. Let $\psi : \mathbb{R} \to \mathbb{C}$ be a Schwartz function and $\hbar > 0$. Then
--
--   $$\int_{-\infty}^{\infty}\int_{-\infty}^{\infty} W(x,p)\,dp\,dx = \int_{-\infty}^{\infty} |\psi(x)|^2\,dx.$$
--
--   For a normalized pure state the right-hand side equals 1: this is the normalization identity of Property 2 in the source, $\int dx \int dp\, W(x,p) = \mathrm{Tr}(\hat\rho)$, since the trace of a pure-state density matrix is the squared norm of the wavefunction.
--
--   **Formalization Note** Both sides are Lebesgue integrals of real-valued functions over $\mathbb{R}$; the left side is an iterated integral. Schwartz regularity is the standing convention under which all displayed integrals exist.
-- source:
--   Wikipedia, "Wigner quasiprobability distribution" (oldid 1376057304), section "Mathematical properties", Property 2, third formula. https://en.wikipedia.org/wiki/Wigner_quasiprobability_distribution

import Mathlib
import Definitions.Def_wigner

open MeasureTheory

namespace Wigner

theorem wigner_norm (ψ : SchwartzMap ℝ ℂ) {ℏ : ℝ} (hℏ : 0 < ℏ) :
    ∫ x, ∫ p, wigner (⇑ψ) ℏ x p = ∫ x, ‖⇑ψ x‖ ^ 2 := by sorry

end Wigner
