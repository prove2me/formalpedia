-- Prove2me | Theorems.Thm_TestableSanitization_Robust_lemma_37
-- name    : TestableSanitization.Robust.lemma_37
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:52:39.20198+00:00
-- url     : https://prove2.me/theorems/108b8e6e-017b-46fb-ae6b-d592b50b0a46
-- title:
--   Lemma 37 — the smoothed classifier $u_{f,\delta}(x)=\mathbb E_{z\sim U}[f(x+\delta z)]$ is $(2\sqrt d/\delta)$-Lipschitz
-- statement:
--   Let $d\ge1$, $\delta>0$, and let $f:\mathbb R^d\to\{\pm1\}$ be measurable. Define the smoothed classifier $u_{f,\delta}(x)=\mathbb E_{z\sim U}[f(x+\delta z)]$, with $U$ the uniform distribution on the closed unit ball. Then $u_{f,\delta}$ is $(2\sqrt d/\delta)$-Lipschitz: for all $x,x'\in\mathbb R^d$,
--   $$|u_{f,\delta}(x)-u_{f,\delta}(x')|\le\frac{2\sqrt d}{\delta}\,\|x-x'\|.$$
--
--   Since $\phi_{f,\delta}(x)=(1-f(x)u_{f,\delta}(x))/2$, Lipschitz continuity of $u$ is what lets estimates of $u$ on a finite grid be interpolated to every point of a cube, which is how the sanitizer's local noise sensitivity estimator achieves uniform accuracy.
--
--   Differences from the source:
--   - encoding: the input space R^d (a dimension, d ≥ 1 as in Lemma 34) → d : ℕ with the hypothesis 1 ≤ d, points in EuclideanSpace ℝ (Fin d); reason: Lean convention for R^d with the Euclidean norm; excludes only the degenerate d = 0
--   - encoding: a measurable f : X → {±1} with a fixed measurable extension to R^d (Appendix B, X ⊆ R^d) → a measurable f : Pt d → ℝ with values ±1 on all of R^d (IsClassifier f); reason: the extension is a measurable ±1 function on R^d and u is defined from it alone; for X = R^d (Theorem 1's setting) it is f itself
--   - encoding: u_{f,δ} is (2√d/δ)-Lipschitz → |u(x) − u(x′)| ≤ (2√d/δ)‖x − x′‖ for all x, x′, with u written as a Bochner integral against U d; reason: the definition of Lipschitz; the integrand is bounded and measurable, so the integral is the expectation
-- source:
--   Cai, Mamali, Sotiraki, Yu, Zampetakis, Testable Sanitization via Boundary Geometry, STOC 2027 submission (manuscript sha256 bcf6434f…), p. 69 (PDF 71), Lemma 37

import Mathlib
import Definitions.Def_TestableSanitization_Robust_Boundary

open MeasureTheory

namespace TestableSanitization.Robust

theorem lemma_37 (d : ℕ) (hd : 1 ≤ d) (δ : ℝ) (hδ : 0 < δ) (f : Pt d → ℝ)
    (hf : IsClassifier f) (x x' : Pt d) :
    |(∫ z, f (x + δ • z) ∂(U d)) - ∫ z, f (x' + δ • z) ∂(U d)| ≤
      2 * Real.sqrt d / δ * ‖x - x'‖ := by sorry

end TestableSanitization.Robust
