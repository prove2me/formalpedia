-- Prove2me | Theorems.Thm_TalagrandConc_QPoints_corollary_3_1_3
-- name    : TalagrandConc.QPoints.corollary_3_1_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:38:40.541594+00:00
-- url     : https://prove2.me/theorems/8df4654b-930d-4354-aa02-fbda8729b0c4
-- title:
--   Corollary 3.1.3 — $\int\min_{i\le q}(q,1/g_i)\,d\mu\prod_{i\le q}\int g_i\,d\mu\le 1$
-- statement:
--   Let $(\Omega,\mu)$ be a probability space and $q\ge 2$ an integer. Let $g_1,\dots,g_q$ be measurable functions on $\Omega$ with $0\le g_i\le 1$. Then
--   $$\int_\Omega \min_{i\le q}\Big(q,\frac1{g_i}\Big)\,d\mu\ \prod_{i\le q}\int_\Omega g_i\,d\mu\le 1,$$
--   where $1/0=+\infty$, so that $\min(q,1/g_i)=q$ where $g_i=0$.
--
--   This is the form of Lemma 3.1.2 used in the induction step of Theorem 3.1.1, with $g_i(\omega)=P(A_i(\omega))/P(B_i)$ and, for $N=1$, with $g_i=\mathbf 1_{A_i}$.
--
--   **Formalization Note** The functions take values in $[0,\infty]$ (`ℝ≥0∞`), which builds in the nonnegativity $g_i\ge0$ that the paper uses implicitly (its applications are ratios of probabilities and indicators); integrals are lower Lebesgue integrals `∫⁻` of measurable functions. The inverse $0^{-1}=\infty$ is that of `ℝ≥0∞`.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 113, Corollary 3.1.3, Eq. (3.1.5)

import Mathlib

namespace TalagrandConc.QPoints

open MeasureTheory
open scoped ENNReal

/-- Corollary 3.1.3 (3.1.5), with `0 ≤ g_i ≤ 1` (values in `ℝ≥0∞`, `1 / 0 = ⊤`). -/
theorem corollary_3_1_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (q : ℕ) (hq : 2 ≤ q) (g : Fin q → Ω → ℝ≥0∞)
    (hg : ∀ i, Measurable (g i)) (hup : ∀ i ω, g i ω ≤ 1) :
    (∫⁻ ω, ⨅ i : Fin q, min (q : ℝ≥0∞) (g i ω)⁻¹ ∂μ) * ∏ i : Fin q, ∫⁻ ω, g i ω ∂μ ≤ 1 := by sorry

end TalagrandConc.QPoints
