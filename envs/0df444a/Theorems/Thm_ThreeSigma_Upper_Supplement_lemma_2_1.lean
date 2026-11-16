-- Prove2me | Theorems.Thm_ThreeSigma_Upper_Supplement_lemma_2_1
-- name    : ThreeSigma.Upper.Supplement.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:15:41.804427+00:00
-- url     : https://prove2.me/theorems/50e0c5a2-8578-47b9-9eff-88feec796092
-- title:
--   Lemma 2.1 — Talagrand's concentration inequality on the cube
-- statement:
--   Let $\varepsilon$ be uniform on $\{-1,1\}^d$ and let $K\subseteq\mathbb R^d$ be closed and convex with $\mathbb P[\varepsilon\in K]>0$. Write $\operatorname{dist}(x,K)=\inf_{y\in K}\|x-y\|_2$ for the Euclidean distance. Then
--   $$\mathbb E\left[\exp\left(\frac{\operatorname{dist}(\varepsilon,K)^2}{16}\right)\right]\le\frac{1}{\mathbb P[\varepsilon\in K]}.$$
--
--   The paper cites this inequality (expositions by Tao and Rothvoss) and uses it in the Claim of §2.2 to show that $\|H\varepsilon\|_1$ is rarely close to its maximum.
--
--   **Formalization Note** $K$ is a set in `EuclideanSpace ℝ (Fin d)`, the distance is `Metric.infDist`, and a sign vector is sent to Euclidean space by `WithLp.toLp 2`.
--
--   Differences from the source:
--   - encoding: ε uniform on {−1,1}^m; ℙ and 𝔼 over ε → uniformProb / uniformAvg: the fraction (average) over the 2^m vectors of signVectors; reason: the uniform law on a finite cube is the normalized count; same values
--   - encoding: K ⊆ ℝ^d with Euclidean distance dist(x,K) = inf_{y∈K} ‖x − y‖₂ → K : Set (EuclideanSpace ℝ (Fin d)), Metric.infDist; reason: EuclideanSpace carries the ℓ2 metric; same distance
-- source:
--   Victor Reis, Zhao Song, Three Standard Deviations Suffice While One Does Not, STOC 2027 submission #393 (October 2026), Lemma 2.1, p. 3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/393.pdf (SHA-256 3be06ff7fede4a6b259a8de8615176523f985a50a464328e2179c71e52153940)

import Definitions.Def_ThreeSigma_Upper_Supplement_Model

namespace ThreeSigma.Upper.Supplement

/-- Lemma 2.1 (Talagrand's concentration inequality), p. 3: for ε uniform on {−1,1}^d and
every closed convex K ⊆ ℝ^d with ℙ[ε ∈ K] > 0, 𝔼[exp(dist(ε,K)²/16)] ≤ 1/ℙ[ε ∈ K].
The distance is Euclidean (Metric.infDist in EuclideanSpace ℝ (Fin d)). -/
theorem lemma_2_1 (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d)))
    (hK_closed : IsClosed K) (hK_convex : Convex ℝ K)
    (hK_pos : 0 < uniformProb (fun ε : Fin d → ℝ => WithLp.toLp 2 ε ∈ K)) :
    uniformAvg (fun ε : Fin d → ℝ => Real.exp (Metric.infDist (WithLp.toLp 2 ε) K ^ 2 / 16)) ≤
      1 / uniformProb (fun ε : Fin d → ℝ => WithLp.toLp 2 ε ∈ K) := by sorry

end ThreeSigma.Upper.Supplement
