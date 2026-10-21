-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P09_integrated_preserves_smoothVectors
-- name    : QAlgorithms.Papers.Independent.Renew46.P09.integrated_preserves_smoothVectors
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:02:54.250987+00:00
-- url     : https://prove2.me/theorems/9e99dcbc-732e-4050-8465-95671dd00c22
-- title:
--   Lemma 1.1: integrated operators preserve smooth vectors
-- statement:
--   Let $G$ be a finite-dimensional real Lie group, let $H$ be a complex Hilbert space, and let $\pi:G\to\mathrm U(H)$ be a strongly continuous unitary representation. Fix a regular left Haar measure $dg$. A vector belongs to $H^\infty$ precisely when its orbit map is smooth. For every continuous compactly supported function $f:G\to\mathbb C$,
--
--   $$
--   \pi(f)H^\infty\subseteq H^\infty,
--   \qquad \pi(f)v=\int_G f(g)\pi(g)v\,dg.
--   $$
--
--   The integral is an $H$-valued integral for each vector $v$. This result asserts preservation of smooth vectors and requires no trace-class hypothesis.
-- source:
--   On the characterization of trace class representations and Schwartz operators, arXiv:1512.02451v1, PDF p. 3, Lemma 1.1

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P09

noncomputable section

open MeasureTheory Filter

open scoped Manifold ContDiff Topology

namespace QAlgorithms.Papers.Independent.Renew46.P09

/-- Lemma 1.1, PDF p.3: every continuous compactly supported test function
preserves smooth vectors. The group is finite dimensional as stipulated at the
start of Section 1; neither trace class nor smoothness of f is assumed. -/
theorem integrated_preserves_smoothVectors
    {E G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [T2Space G]
    [ChartedSpace E G] [LieGroup 𝓘(ℝ, E) ∞ G]
    [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (mu : Measure G) [mu.IsHaarMeasure] [mu.Regular]
    (pi : G →* (H ≃ₗᵢ[ℂ] H))
    (hstrong : ∀ v : H, Continuous (fun g : G => pi g v))
    (f : G → ℂ) (hf : Continuous f) (hsupp : HasCompactSupport f)
    (v : H) (hv : HasSmoothOrbit (E := E) (fun g => pi g) v) :
    HasSmoothOrbit (E := E) (fun g => pi g)
      (integratedVector mu (fun g => pi g) f v) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P09

end
