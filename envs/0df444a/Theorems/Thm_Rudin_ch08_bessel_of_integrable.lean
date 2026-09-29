-- Prove2me | Theorems.Thm_Rudin_ch08_bessel_of_integrable
-- name    : Rudin.ch08_bessel_of_integrable
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-14T05:19:05.271739+00:00
-- url     : https://prove2.me/theorems/c92eb02a-079c-4235-a36d-64c6dc83c34b
-- title:
--   Best mean-square approximation and Bessel's inequality (Rudin 8.11, 8.12), corrected
-- statement:
--   **Best approximation in the mean, and Bessel's inequality.** Let $\{\varphi_m\}$ be an orthonormal system on $[a,b]$, with $a \le b$, and let $f$ be square-integrable on $[a,b]$. Write
--   $$c_m \;=\; \int_a^b f\,\overline{\varphi_m}$$
--   for the Fourier coefficients of $f$ relative to the system, and let $\gamma_0,\dots,\gamma_{n-1}$ be arbitrary complex numbers. Then:
--
--   1. *(Best approximation.)* The partial sum $s_n = \sum_{m<n} c_m \varphi_m$ is at least as close to $f$ in mean square as any other linear combination:
--   $$\int_a^b \Bigl\| f - \sum_{m<n} c_m\varphi_m \Bigr\|^2 \;\le\; \int_a^b \Bigl\| f - \sum_{m<n} \gamma_m\varphi_m \Bigr\|^2 .$$
--   2. *(Bessel's inequality.)* $\displaystyle\sum_{m<n} |c_m|^2 \;\le\; \int_a^b \|f\|^2 .$
--
--   Both follow from the identity $\int \|f - \sum \gamma_m\varphi_m\|^2 = \int\|f\|^2 - \sum|c_m|^2 + \sum|\gamma_m - c_m|^2$.
--
--   **Formalization note.** The integrability hypotheses are needed because the interval integral of a non-integrable function is $0$ by convention, which makes the inequality fail. On $[0,1]$ with the orthonormal system $\varphi_m(x) = e^{2\pi i m x}$ and $f(x) = x^{-1/2}$, the coefficient $c_0 = \int_0^1 f = 2$, while $\int_0^1 \|f\|^2 = \int_0^1 dx/x$ is not integrable and evaluates to $0$, so Bessel's inequality would read $4 \le 0$. Assuming $f$ and $\|f\|^2$ interval-integrable on $[a,b]$ — and likewise for each $\varphi_m$ — matches the hypotheses already carried by `Rudin.ch08_parseval`.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd ed., Chapter 8, Theorems 8.11 and 8.12, pp. 187-188. Corrected form of the platform theorem Rudin.ch08_bessel (disproved).

import Mathlib
import Definitions.Def_Rudin_ch08_fourier

open Filter Topology

namespace Rudin

/-- Rudin, Theorems 8.11 and 8.12, with the integrability hypotheses of Chapter 8: among all
linear combinations of `φ 0, …, φ (n-1)` the partial sum of the Fourier series of `f` is the best
approximation in the mean square sense, and Bessel's inequality holds. -/
theorem ch08_bessel_of_integrable (a b : ℝ) (hab : a ≤ b) (φ : ℕ → ℝ → ℂ)
    (hφ : IsOrthonormalSystem φ a b)
    (hφint : ∀ m, IntervalIntegrable (φ m) MeasureTheory.volume a b)
    (hφ2 : ∀ m, IntervalIntegrable (fun x => ‖φ m x‖ ^ 2) MeasureTheory.volume a b)
    (f : ℝ → ℂ) (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hf2 : IntervalIntegrable (fun x => ‖f x‖ ^ 2) MeasureTheory.volume a b)
    (n : ℕ) (γ : ℕ → ℂ) :
    (∫ x in a..b, ‖f x - ∑ m ∈ Finset.range n, genFourierCoeff f φ a b m * φ m x‖ ^ 2) ≤
      (∫ x in a..b, ‖f x - ∑ m ∈ Finset.range n, γ m * φ m x‖ ^ 2) ∧
    (∑ m ∈ Finset.range n, ‖genFourierCoeff f φ a b m‖ ^ 2) ≤ ∫ x in a..b, ‖f x‖ ^ 2 := by sorry

end Rudin
