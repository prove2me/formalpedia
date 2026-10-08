-- Prove2me | Theorems.Thm_SmoothedSimplex_Shadow_points_under_plane
-- name    : SmoothedSimplex.Shadow.points_under_plane
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T13:34:43.815526+00:00
-- url     : https://prove2.me/theorems/4f1436e9-4b06-408c-867c-91a3d5b971e4
-- title:
--   Lemma 4.2.3 — points under plane
-- statement:
--   Let $n>d\ge3$ and let $\mu_{d+1},\dots,\mu_n$ be Gaussian distributions in $\mathbb R^d$ of standard deviation $\sigma$ with $0<\sigma\le1/(3\sqrt{d\ln n})$, centered at points of norm at most $1$. Let $q$ be a unit vector, $s\ge0$, and let $\omega_1,\omega_2$ be unit vectors with $\langle\omega_1|q\rangle\ge0$ and $\langle\omega_2|q\rangle\ge0$. Then
--
--   $$
--   \frac{\prod_{j>d}\int_{a_j}\big[\langle\omega_2|a_j\rangle\le s\langle\omega_2|q\rangle\big]\mu_j(a_j)\,da_j}{\prod_{j>d}\int_{a_j}\big[\langle\omega_1|a_j\rangle\le s\langle\omega_1|q\rangle\big]\mu_j(a_j)\,da_j}\ \ge\ 1-\frac{8n(1+s)\|\omega_1-\omega_2\|}{3\sigma^2}.
--   $$
--
--   Tilting the hyperplane slightly changes the probability that all remaining points lie beneath it only slightly; this controls one factor of the density in Lemma 4.2.2.
--
--   **Formalization Note** The hypothesis $\sigma\le1/(3\sqrt{d\ln n})$ (the standing assumption of Section 4, from the first line of the proof of Theorem 4.0.1) is added: without a bound on $\sigma$ the lemma is false (with $n=4$, $d=3$, $s=0$, $\|\bar a_4\|=1$, $\omega_1\perp\bar a_4$ and $\omega_2$ tilted by a small angle $\delta$ towards $\bar a_4$, the ratio is about $1-0.80\,\delta/\sigma$, below $1-32\delta/(3\sigma^2)$ at $\sigma=100$), and its proof uses Lemma 2.4.11, which needs $\sigma\le1$. $q$ is the reference unit vector of Section 2.5. The ratio is cross-multiplied.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Lemma 4.2.3, printed p. 54 (PDF p. 54)

import Mathlib
import Definitions.Def_SmoothedSimplex_Shadow_underPlaneMass

namespace SmoothedSimplex.Shadow

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

/-- **Lemma 4.2.3 (Points under plane)** (Spielman & Teng, arXiv:cs/0111050v7, Lemma 4.2.3,
printed p. 54, PDF p. 54). For `n > d`, let `µ_{d+1}, …, µₙ` be Gaussian distributions in `ℝ^d` of
standard deviation `σ` centered at points of norm at most 1. Let `s ≥ 0` and let `ω₁` and `ω₂` be
unit vectors such that `⟨ω₁|q⟩` and `⟨ω₂|q⟩` are non-negative. Then
`∏_{j>d} ∫ [⟨ω₂|aⱼ⟩ ≤ s⟨ω₂|q⟩] µⱼ / ∏_{j>d} ∫ [⟨ω₁|aⱼ⟩ ≤ s⟨ω₁|q⟩] µⱼ ≥ 1 − 8n(1 + s)‖ω₁ − ω₂‖/(3σ²)`.

**Formalization Note.**
* **Added hypothesis `σ ≤ 1/(3√(d ln n))`** (with `d ≥ 3`), §4's standing assumption (first line
  of the proof of Theorem 4.0.1, p. 39). Without a bound on `σ` the lemma is false: with `n = 4`,
  `d = 3`, `s = 0`, `‖ā₄‖ = 1`, `ω₁ ⟂ ā₄` and `ω₂` tilted by `δ` towards `ā₄`, the ratio is about
  `1 − 0.80δ/σ`, below `1 − 32δ/(3σ²)` at `σ = 100`. The proof uses Lemma 2.4.11, which needs
  `σ ≤ 1`; the standing assumption implies it.
* `q` is the reference unit vector of §2.5 (`‖q‖ = 1`, used in the proof's `‖sq − āⱼ‖ ≤ s + 1`).
* The centers `ā₁, …, ā_d` are unconstrained (they do not enter). The ratio is cross-multiplied,
  with the products as real numbers. -/
theorem points_under_plane {d n : ℕ} (hd : 3 ≤ d) (hn : d < n) (σ : ℝ) (hσ : 0 < σ)
    (hσ' : σ ≤ 1 / (3 * Real.sqrt ((d : ℝ) * Real.log n)))
    (abar : Fin n → EuclideanSpace ℝ (Fin d)) (habar : ∀ j : Fin n, d ≤ j.val → ‖abar j‖ ≤ 1)
    (q : EuclideanSpace ℝ (Fin d)) (hq : ‖q‖ = 1) (s : ℝ) (hs : 0 ≤ s)
    (ω₁ ω₂ : EuclideanSpace ℝ (Fin d)) (hω₁ : ‖ω₁‖ = 1) (hω₂ : ‖ω₂‖ = 1)
    (h₁ : 0 ≤ ⟪ω₁, q⟫) (h₂ : 0 ≤ ⟪ω₂, q⟫) :
    (1 - 8 * n * (1 + s) * ‖ω₁ - ω₂‖ / (3 * σ ^ 2)) * (underPlaneMass abar σ ω₁ q s).toReal ≤
      (underPlaneMass abar σ ω₂ q s).toReal := by sorry

end SmoothedSimplex.Shadow
