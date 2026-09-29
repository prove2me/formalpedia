-- Prove2me | Theorems.Thm_Rudin_ch08_bessel
-- name    : Rudin.ch08_bessel
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-09-13T02:27:03.73758+00:00
-- url     : https://prove2.me/theorems/55423b26-0ac1-47a1-8f29-8f4ff1777aab
-- title:
--   Theorems 8.11-8.12 — best mean-square approximation and Bessel's inequality
-- statement:
--   Let $\{\varphi_n\}$ be orthonormal on $[a,b]$ and let $c_m$ be the Fourier coefficients of $f$. Among all combinations $\sum_{m<n} \gamma_m \varphi_m$, the choice $\gamma_m = c_m$ minimizes $\int_a^b |f - \sum \gamma_m\varphi_m|^2$; and $\sum_{m<n} |c_m|^2 \le \int_a^b |f|^2$ for every $n$ (Bessel's inequality).
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 8, pp. 187-188, Theorems 8.11 and 8.12

import Mathlib
import Definitions.Def_Rudin_ch08_fourier

open Filter Topology

namespace Rudin

/-- Rudin, Theorems 8.11 and 8.12: among all linear combinations of `φ 0, …, φ (n-1)` the
partial sum of the Fourier series of `f` is the best approximation in the mean square sense, and
Bessel's inequality `∑ |cₘ|² ≤ ∫ |f|²` holds. -/
theorem ch08_bessel (a b : ℝ) (hab : a ≤ b) (φ : ℕ → ℝ → ℂ) (hφ : IsOrthonormalSystem φ a b)
    (f : ℝ → ℂ) (n : ℕ) (γ : ℕ → ℂ) :
    (∫ x in a..b, ‖f x - ∑ m ∈ Finset.range n, genFourierCoeff f φ a b m * φ m x‖ ^ 2) ≤
      (∫ x in a..b, ‖f x - ∑ m ∈ Finset.range n, γ m * φ m x‖ ^ 2) ∧
    (∑ m ∈ Finset.range n, ‖genFourierCoeff f φ a b m‖ ^ 2) ≤ ∫ x in a..b, ‖f x‖ ^ 2 := by sorry

end Rudin
