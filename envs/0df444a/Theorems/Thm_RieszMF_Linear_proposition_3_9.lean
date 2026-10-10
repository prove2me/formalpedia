-- Prove2me | Theorems.Thm_RieszMF_Linear_proposition_3_9
-- name    : RieszMF.Linear.proposition_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:15:54.128038+00:00
-- url     : https://prove2.me/theorems/c36e5941-6910-4fd8-a076-b1d23e7f20f4
-- title:
--   Proposition 3.9, p. 14 — sharp Euclidean log-Sobolev inequality with parameter $a$, and its equality case
-- statement:
--   Let $a>0$ and $f\in H^1(\mathbb R^d)$ (complex valued). Then
--   $$\int_{\mathbb R^d}|f(x)|^2\log\Big(\frac{|f(x)|^2}{\|f\|_{L^2}^2}\Big)dx+\Big(d+\frac{d\log a}{2}\Big)\int_{\mathbb R^d}|f(x)|^2dx\le\frac a\pi\int_{\mathbb R^d}|\nabla f(x)|^2dx.$$
--   Moreover, equality holds if and only if $f$ is a scalar multiple and translate of $f_a(x)=a^{-d/4}e^{-\pi|x|^2/2a}$, i.e. $f(x)=c\,f_a(x-x_0)$ a.e. for some $c\in\mathbb C$ and $x_0\in\mathbb R^d$.
--
--   This is Gross's logarithmic Sobolev inequality in the sharp Euclidean form of Carlen–Loss; the proof of Proposition 3.8 applies it at every time with $f=|\mu^t|^{r(t)/2}$.
--
--   **Formalization Note.** $H^1$ is encoded as $f\in L^2$ with a weak gradient $w=(w_1,\dots,w_d)\in L^2$: $\int f\,\partial_j\varphi=-\int w_j\varphi$ for every smooth compactly supported real $\varphi$, and $|\nabla f|^2=\sum_j|w_j|^2$. The convention $0\log0=0$ is Lean's $\log 0=0$. The entropy integral is assumed absolutely convergent: for $f\in H^1$ its positive part is always finite (Sobolev embedding), so the excluded case is exactly the one where the left side is $-\infty$ and the inequality holds trivially.
-- source:
--   Rosenzweig & Serfaty, Global-in-time mean-field convergence for singular Riesz-type diffusive flows, arXiv:2108.09878v1, p. 14, Proposition 3.9, (3.24)

import Mathlib
import Definitions.Def_RieszMF_Linear_Setting

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped NNReal ENNReal FourierTransform Laplacian

namespace RieszMF.Linear

theorem proposition_3_9 (d : ℕ) (a : ℝ) (ha : 0 < a) (f : E d → ℂ) (hf : MemLp f 2 volume)
    (w : Fin d → E d → ℂ) (hw : ∀ j, MemLp (w j) 2 volume)
    (hweak : ∀ φ : E d → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      ∀ j : Fin d, ∫ x, f x * ((fderiv ℝ φ x (ebasis d j) : ℝ) : ℂ) = -∫ x, w j x * ((φ x : ℝ) : ℂ))
    (hint : Integrable
      (fun x => ‖f x‖ ^ 2 * Real.log (‖f x‖ ^ 2 / ∫ y, ‖f y‖ ^ 2)) volume) :
    (∫ x, ‖f x‖ ^ 2 * Real.log (‖f x‖ ^ 2 / ∫ y, ‖f y‖ ^ 2))
        + ((d : ℝ) + d * Real.log a / 2) * ∫ x, ‖f x‖ ^ 2
      ≤ a / Real.pi * ∫ x, ∑ j, ‖w j x‖ ^ 2 ∧
    ((∫ x, ‖f x‖ ^ 2 * Real.log (‖f x‖ ^ 2 / ∫ y, ‖f y‖ ^ 2))
        + ((d : ℝ) + d * Real.log a / 2) * ∫ x, ‖f x‖ ^ 2
      = a / Real.pi * ∫ x, ∑ j, ‖w j x‖ ^ 2 ↔
      ∃ c : ℂ, ∃ x₀ : E d, f =ᵐ[volume] fun x =>
        c * ((a ^ (-(d : ℝ) / 4) * Real.exp (-Real.pi * ‖x - x₀‖ ^ 2 / (2 * a)) : ℝ) : ℂ)) := by sorry

end RieszMF.Linear
