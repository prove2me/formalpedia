-- Prove2me | Theorems.Thm_SmoothBerr_lemma_5_5
-- name    : SmoothBerr.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:27:39.701507+00:00
-- url     : https://prove2.me/theorems/82c18d02-3fd1-4a72-bc7a-c86b3546a92c
-- title:
--   Lemma 5.5 — upper bound: $\mathbb P[\|\hat A^{-1}v\|_2\ge t,\ \|\hat A^{-1}\|_2\le s\sqrt n]\le 3s^2/t^2$
-- statement:
--   Let $n\ge8$, let $A\in\mathbb R^{n\times n}$ have iid $\mathcal N(0,1)$ entries, let $\Delta$ be independent of $A$ with $\|\Delta\|_2\le\sqrt n/2$ almost surely, and set $\hat A=A+\Delta$. Let $v\in\mathbb S^{n-1}$ be a uniformly random unit vector independent of $(A,\Delta)$. For every $s,t\ge1$,
--   $$
--   \mathbb P\Big[\|\hat A^{-1}v\|_2\ge t\ \text{ and }\ \|\hat A^{-1}\|_2\le s\sqrt n\Big]\le\frac{3s^2}{t^2}.
--   $$
--   A random direction cannot see a large value of $\hat A^{-1}$ while the spectral norm of $\hat A^{-1}$ is small. Combined with Lemma 5.4 it yields Theorem 4.2.
--
--   **Formalization Note** The law of $v$ is any probability measure on Euclidean space that is supported on the unit sphere and invariant under every linear isometry (the published `IsUniformOnUnitSphere`), i.e. the normalized surface measure. The level $t$ is named $\tau$ in Lean.
--
--   Differences from the source:
--   - reading: Â = A + Δ "defined as in Theorem 4.2" → n ≥ 8, A with law gaussianMatrix n n, Δ with an arbitrary probability law ν such that ‖Δ‖₂ ≤ √n/2 ν-a.s., and the product law gaussianMatrix n n ⊗ ν; reason: the setting of Theorem 4.2 (p.5): Δ independent of A with ‖Δ‖₂ ≤ √n/2 almost surely
--   - encoding: v ∈ S^{n−1} uniformly random, independent of (A, Δ) → a probability law σ on EuclideanSpace ℝ (Fin n) with IsUniformOnUnitSphere σ id, and the product law (gaussianMatrix n n ⊗ ν) ⊗ σ; reason: rotation invariance plus support on the sphere characterizes the uniform law
--   - encoding: Â⁻¹ → Mathlib's total inverse (0 on singular Â); reason: Â is singular only on a null event (A has a density, independent of Δ); the event is empty there
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), Lemma 5.5, p.13

import Mathlib
import Definitions.Def_GaussianMatrix_basic
import Definitions.Def_OnlineConvexOpt_BanditConvex_UniformOnUnitSphere_v2
import Definitions.Def_ApproxVI_euclNorm

open MeasureTheory ProbabilityTheory Matrix GaussianMatrix

namespace SmoothBerr

/-- **Lemma 5.5 (Upper bound)** (Dereziński, Mahoney, Meyer, Musco, *From smoothed analysis to backward error: The power of adaptive perturbations*, manuscript of 3 Nov 2026, sha256 9575cd20…, Lemma 5.5, p.13).

Let `Â = A + Δ` be as in Theorem 4.2 (`n ≥ 8`, `A` with iid `N(0,1)` entries, `Δ` independent of
`A` with `‖Δ‖₂ ≤ √n/2` almost surely), and let `v ∈ S^{n−1}` be a uniformly random unit vector
independent of `(A, Δ)`. For every `s, t ≥ 1`,
`P[‖Â⁻¹v‖₂ ≥ t and ‖Â⁻¹‖₂ ≤ s√n] ≤ 3s²/t²`.

**Formalization Note** The law `σ` of `v` is any probability measure on `EuclideanSpace ℝ (Fin n)`
with `IsUniformOnUnitSphere σ id` (published `OnlineConvexOpt.BanditConvex.IsUniformOnUnitSphere`:
supported on the unit sphere and invariant under every linear isometry, which characterizes the
normalized surface measure). Independence is the product measure `(gaussianMatrix n n ⊗ ν) ⊗ σ`.
The paper's level `t` is named `τ`. `‖Â⁻¹v‖₂` is `ApproxVI.euclNorm` of the coordinate vector `v.ofLp`;
`‖Â⁻¹‖₂` is `specNorm`; `Â⁻¹` is Mathlib's total inverse (`0` on the null event that `Â` is
singular). -/
theorem lemma_5_5 (n : ℕ) (hn : 8 ≤ n) (ν : Measure (Fin n → Fin n → ℝ)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ Δ ∂ν, specNorm (Matrix.of Δ) ≤ Real.sqrt n / 2)
    (σ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure σ]
    (hσ : OnlineConvexOpt.BanditConvex.IsUniformOnUnitSphere σ id)
    (s τ : ℝ) (hs : 1 ≤ s) (hτ : 1 ≤ τ) :
    (((gaussianMatrix n n).prod ν).prod σ)
        {q | τ ≤ ApproxVI.euclNorm ((Matrix.of q.1.1 + Matrix.of q.1.2)⁻¹ *ᵥ q.2.ofLp) ∧
          specNorm ((Matrix.of q.1.1 + Matrix.of q.1.2)⁻¹) ≤ s * Real.sqrt n} ≤
      ENNReal.ofReal (3 * s ^ 2 / τ ^ 2) := by sorry

end SmoothBerr
