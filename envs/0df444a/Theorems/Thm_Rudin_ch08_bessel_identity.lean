-- Prove2me | Theorems.Thm_Rudin_ch08_bessel_identity
-- name    : Rudin.ch08_bessel_identity
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-18T14:32:35.762831+00:00
-- url     : https://prove2.me/theorems/75e24490-bc41-4f4d-a4e7-eb5e7176e8c8
-- title:
--   The Bessel identity behind Rudin 8.11-8.12: the exact mean-square error of a linear combination
-- statement:
--   **The Bessel identity (Rudin, Theorems 8.11 and 8.12).** Let $\{\varphi_m\}$ be an orthonormal system on $[a,b]$, $a \le b$: $\int_a^b \varphi_n \overline{\varphi_m} = 0$ for $n \ne m$ and $\int_a^b |\varphi_n|^2 = 1$. Let $f$ be square-integrable on $[a,b]$ and let
--   $$c_m \;=\; \int_a^b f\,\overline{\varphi_m}$$
--   be its Fourier coefficients relative to the system. Then for every $n$ and every choice of complex numbers $\gamma_0,\dots,\gamma_{n-1}$,
--   $$\int_a^b \Bigl\| f - \sum_{m<n} \gamma_m \varphi_m \Bigr\|^2 \;=\; \int_a^b \|f\|^2 \;-\; \sum_{m<n} |c_m|^2 \;+\; \sum_{m<n} |\gamma_m - c_m|^2 .$$
--
--   This single identity is the computation behind both of Rudin's theorems. Taking $\gamma_m = c_m$ kills the last sum and shows that the partial sum of the Fourier series is the orthogonal projection of $f$ onto the span of $\varphi_0,\dots,\varphi_{n-1}$: it is the *best mean-square approximation*, since the last sum is nonnegative for every other choice of $\gamma$ (Theorem 8.11). Since the left-hand side is nonnegative, taking $\gamma = c$ also gives $\sum_{m<n}|c_m|^2 \le \int_a^b \|f\|^2$, which is Bessel's inequality (Theorem 8.12). The identity moreover quantifies the defect: the mean-square error of an arbitrary approximation exceeds the optimal one by exactly $\sum_{m<n} |\gamma_m - c_m|^2$.
--
--   **Formalization notes.** Integrability hypotheses on $f$ are genuinely needed, not decoration: the interval integral of a non-integrable function is $0$ by convention, and without them the statement is false (on $[0,1]$ with $\varphi_m(x) = e^{2\pi i m x}$ and $f(x) = x^{-3/4}$ one has $c_0 = 4$ while $\int_0^1 \|f\|^2$ evaluates to $0$). The hypothesis `hf` supplies the measurability of $f$ and `hf2` its square-integrability. Similarly some measurability of the system is required, supplied by `hφint`; no separate square-integrability hypothesis on the $\varphi_m$ is needed, because $\int_a^b |\varphi_m|^2 = 1 \ne 0$ already forces $|\varphi_m|^2$ to be integrable.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 8, pp. 187-188, Theorems 8.11 and 8.12 (the identity displayed in the proof of 8.11)

import Mathlib
import Definitions.Def_Rudin_ch08_fourier

open Filter Topology

namespace Rudin

/-- Rudin, Theorems 8.11 and 8.12, in the sharp form of the identity that proves them: for an
orthonormal system `φ` on `[a, b]`, a square-integrable `f` with Fourier coefficients
`cₘ = ∫ f conj(φ m)`, and arbitrary coefficients `γ`,
`∫ ‖f - ∑_{m<n} γₘ φₘ‖² = ∫ ‖f‖² - ∑_{m<n} |cₘ|² + ∑_{m<n} |γₘ - cₘ|²`. -/
theorem ch08_bessel_identity (a b : ℝ) (hab : a ≤ b) (φ : ℕ → ℝ → ℂ)
    (hφ : IsOrthonormalSystem φ a b)
    (hφint : ∀ m, IntervalIntegrable (φ m) MeasureTheory.volume a b)
    (f : ℝ → ℂ) (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hf2 : IntervalIntegrable (fun x => ‖f x‖ ^ 2) MeasureTheory.volume a b)
    (n : ℕ) (γ : ℕ → ℂ) :
    (∫ x in a..b, ‖f x - ∑ m ∈ Finset.range n, γ m * φ m x‖ ^ 2) =
      (∫ x in a..b, ‖f x‖ ^ 2) - (∑ m ∈ Finset.range n, ‖genFourierCoeff f φ a b m‖ ^ 2)
        + ∑ m ∈ Finset.range n, ‖γ m - genFourierCoeff f φ a b m‖ ^ 2 := by sorry

end Rudin
