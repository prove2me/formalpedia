-- Prove2me | Theorems.Thm_RSListDecodingCapacity_AllRates_lemma_3_9
-- name    : RSListDecodingCapacity.AllRates.lemma_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:59.889241+00:00
-- url     : https://prove2.me/theorems/860df2c7-8dd6-46b4-ae64-fc6f8b949c0a
-- title:
--   Lemma 3.9 — the mean of the uniform distribution on a simplex is its centroid
-- statement:
--   Let $v_0,\dots,v_{d-1}$ ($d\ge1$) be affinely independent points of a Euclidean space, so that $S=\mathrm{conv}\{v_0,\dots,v_{d-1}\}$ is a $(d-1)$-dimensional simplex, and let $X$ be uniformly distributed on $S$. Then
--   $$\mathbb E[X]=\frac1d\sum_{i=0}^{d-1}v_i ,$$
--   the centroid of $S$.
--
--   In the proof of Lemma 3.3 it gives the expected coordinate sum of a uniform point of $S_W$, which a Markov bound turns into the volume estimate for $\mathcal B$. The same statement is Lemma A.1 of the appendix.
--
--   **Formalization Note** "Uniformly distributed on $S$" is `MeasureTheory.pdf.IsUniform X S P μH[d−1]`: the law of $X$ is the $(d-1)$-dimensional Hausdorff measure restricted to $S$ and normalized. In $\mathbb R^{d-1}$ this measure is a constant multiple of Lebesgue measure, so the normalized measure is the uniform distribution of the source; in a larger ambient space it is the intrinsic (affine-hull) volume.
--
--   Differences from the source:
--   - generalization: a (d−1)-dimensional simplex, used in ℝ^(d−1) → a simplex with affinely independent vertices in any Euclidean space ℝ^N; reason: for N = d − 1 this is the source's setting; for larger N the uniform distribution is taken with respect to intrinsic (d−1)-dimensional volume
--   - reading: X uniformly distributed on S → the law of X is the normalized (d−1)-dimensional Hausdorff measure on S (MeasureTheory.pdf.IsUniform); reason: normalized (d−1)-dimensional volume on S; on ℝ^(d−1) Hausdorff measure of full dimension is a multiple of Lebesgue measure, and the normalization cancels the constant
-- source:
--   Joshua Brakensiek, Yeyuan Chen, Aaron Putterman, Zihan Zhang, Kai Zhe Zheng, Algorithmic List Decoding of Reed–Solomon Codes up to Capacity, STOC 2027 submission #565 (October 2026), p.19, Lemma 3.9 (= Lemma A.1, pp.34–35)

import Mathlib

open MeasureTheory

namespace RSListDecodingCapacity.AllRates

/-- **Lemma 3.9** (Brakensiek–Chen–Putterman–Zhang–Zheng, STOC 2027 submission #565, p.19; repeated
as Lemma A.1, p.35). Let `S = conv{v₀, …, v_{d−1}}` be a `(d − 1)`-dimensional simplex (affinely
independent vertices) in a Euclidean space, and let `X` be uniformly distributed on `S`, i.e. with
law the normalized `(d − 1)`-dimensional Hausdorff measure on `S`. Then
`E[X] = (1/d) ∑_{i=0}^{d−1} vᵢ`, the centroid of `S`. -/
theorem lemma_3_9 {N d : ℕ} (hd : 1 ≤ d) (v : Fin d → EuclideanSpace ℝ (Fin N))
    (hv : AffineIndependent ℝ v) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → EuclideanSpace ℝ (Fin N))
    (hX : MeasureTheory.pdf.IsUniform X (convexHull ℝ (Set.range v)) P
      (Measure.hausdorffMeasure ((d : ℝ) - 1))) :
    ∫ ω, X ω ∂P = (1 / (d : ℝ)) • ∑ i, v i := by sorry

end RSListDecodingCapacity.AllRates
