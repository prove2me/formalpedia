-- Prove2me | Theorems.Thm_UnphysicalHilbert_eq27_28_moments
-- name    : UnphysicalHilbert.eq27_28_moments
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T21:09:44.997323+00:00
-- url     : https://prove2.me/theorems/8f8c4f3c-31fa-47db-a794-a542874fa209
-- title:
--   Eqs. (27)–(28) — Gaussian moments are finite, Lorentzian moments diverge
-- statement:
--   Let $\psi(x)=\sqrt{e^{-x^2}/\sqrt\pi}$ and $\phi(y)=1/\sqrt{\pi(y^2+1)}$. Then
--
--   1. $\displaystyle\int_{\mathbb R}\psi(x)^2\,dx=1$ and $\displaystyle\int_{\mathbb R}\phi(y)^2\,dy=1$;
--   2. for every $n\in\mathbb N$, $\displaystyle\int_{\mathbb R}|x|^n\,\psi(x)^2\,dx<\infty$;
--   3. for every $n\ge2$, $\displaystyle\int_{\mathbb R}|y|^n\,\phi(y)^2\,dy=\infty$.
--
--   The Gaussian state has finite position moments of all orders, while the Lorentzian state has infinite position moments from the second on (in particular infinite $\langle X^2\rangle$).
--
--   **Formalization Note** Finiteness of $\int g$ for a nonnegative $g$ is expressed as Lebesgue integrability of $g$, and infiniteness as its failure.
-- source:
--   G. Carcassi, C. A. Aidala, F. Calderón, *The unphysicality of Hilbert spaces*, arXiv:2308.06669v3 [quant-ph], 22 Dec 2024, https://arxiv.org/abs/2308.06669, Section VI, pp. 11–12, eqs. (27)–(28) and the paragraph following them

import Definitions.Def_UnphysicalHilbert_Position

namespace UnphysicalHilbert

open MeasureTheory

/-- Equations (27)–(28): both wave functions are normalized; the Gaussian state has finite
moments of every order, while the Lorentzian state has divergent moments of every order
`n ≥ 2`. -/
theorem eq27_28_moments :
    ∫ x, gaussianWave x ^ 2 = 1 ∧ ∫ y, lorentzianWave y ^ 2 = 1 ∧
    (∀ n : ℕ, Integrable (fun x : ℝ => |x| ^ n * gaussianWave x ^ 2)) ∧
    (∀ n : ℕ, 2 ≤ n → ¬ Integrable (fun y : ℝ => |y| ^ n * lorentzianWave y ^ 2)) := by
  sorry

end UnphysicalHilbert
