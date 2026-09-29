-- Prove2me | Theorems.Thm_Rudin_ch11_parseval_complete
-- name    : Rudin.ch11_parseval_complete
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T02:42:38.027673+00:00
-- url     : https://prove2.me/theorems/72a4662e-5a22-4018-ac98-50677f187ed0
-- title:
--   Theorem 11.45 — Parseval's identity for a complete orthonormal system
-- statement:
--   Let $\{\varphi_n\}$ be a complete orthonormal system in $\mathscr{L}^2(\mu)$ and let $c_n = \int f\varphi_n\,d\mu$ be the Fourier coefficients of $f \in \mathscr{L}^2(\mu)$. Then $\sum_n c_n^2 = \int f^2\,d\mu$; the Fourier series of $f$ converges to $f$ in the mean.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 11, p. 331, Theorems 11.43 and 11.45

import Mathlib
import Definitions.Def_Rudin_ch11_L2

open Filter Topology MeasureTheory

namespace Rudin

/-- Rudin, Theorem 11.45: if `{φₙ}` is a complete orthonormal set in `ℒ²(μ)` and `cₙ` are the
Fourier coefficients of `f ∈ ℒ²(μ)`, then `∑ cₙ² = ∫ f² dμ` (Parseval's identity). -/
theorem ch11_parseval_complete {X : Type*} [MeasurableSpace X] (μ : Measure X) (φ : ℕ → X → ℝ)
    (hmem : ∀ n, MemL2 μ (φ n))
    (horth : ∀ m n, m ≠ n → (∫ x, φ m x * φ n x ∂μ) = 0)
    (hnorm : ∀ n, (∫ x, (φ n x) ^ 2 ∂μ) = 1)
    (hcomplete : ∀ g : X → ℝ, MemL2 μ g → (∀ n, (∫ x, g x * φ n x ∂μ) = 0) → L2Norm μ g = 0)
    (f : X → ℝ) (hf : MemL2 μ f) (c : ℕ → ℝ) (hc : ∀ n, c n = ∫ x, f x * φ n x ∂μ) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, (c n) ^ 2) atTop (𝓝 (∫ x, (f x) ^ 2 ∂μ)) := by sorry

end Rudin
