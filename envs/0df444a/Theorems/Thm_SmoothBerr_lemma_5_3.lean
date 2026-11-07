-- Prove2me | Theorems.Thm_SmoothBerr_lemma_5_3
-- name    : SmoothBerr.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:28:01.319884+00:00
-- url     : https://prove2.me/theorems/ccfa6241-dac1-4146-ae75-4df46837ef92
-- title:
--   Lemma 5.3 — inverse Frobenius estimation needs $>3n/32$ paired matvecs (corrected: $n\ge1$)
-- statement:
--   Let $A\in\mathbb R^{n\times n}$ have iid $\mathcal N(0,1)$ entries, let $\Delta\in\mathbb R^{n\times n}$ be independent of $A$ with $\|\Delta\|_2\le\sqrt n/3$ almost surely, and set $\hat A:=A+\Delta$, with $n\ge1$. There is a universal constant $\rho>0$ such that every randomized estimator $\hat F$ using at most $t\le 3n/32$ paired matvecs with $\hat A$ satisfies
--   $$
--   \mathbb P\Big[\hat F\notin\big[\tfrac12\|\hat A^{-1}\|_F^2,\ 2\|\hat A^{-1}\|_F^2\big]\Big]\ge\rho .
--   $$
--   Estimating the Frobenius norm of the inverse within a factor of $2$ requires a linear number of matvecs; Theorem 4.1 reduces this estimation problem to solving linear systems.
--
--   **Formalization Note** An estimator is a randomized adaptive paired matvec algorithm with no input and real output, whose seed is independent of $(A,\Delta)$.
--
--   Differences from the source:
--   - correction: any n → 1 ≤ n; reason: false at n = 0: Â is the empty matrix, ‖Â⁻¹‖_F² = 0, and the estimator F̂ ≡ 0 lies in [0, 0] with probability 1
--   - encoding: at most t ≤ 3n/32 paired matvecs → exactly t paired steps with (t : ℝ) ≤ 3n/32; reason: an estimator with fewer steps ignores its last answers
--   - reading: a randomized algorithm succeeding "with probability" → a seed ω drawn from a probability law μ on a measurable space Ω, independent of the matrices; queries and output measurable jointly in the seed and the answers; reason: the measurability that a probability of success presupposes; the seed is the algorithm's own randomness
--   - encoding: a universal constant ρ > 0 → ∃ ρ > 0 chosen before n, ν, t and the estimator; reason: §3, p.4
--   - encoding: Â⁻¹ → Mathlib's total inverse (0 on singular Â); reason: Â is singular only on a null event (A has a density, independent of Δ)
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), Lemma 5.3, p.11

import Mathlib
import Definitions.Def_GaussianMatrix_basic
import Definitions.Def_SmoothBerr_PairedMatvecAlg

open MeasureTheory ProbabilityTheory Matrix GaussianMatrix

namespace SmoothBerr

/-- **Lemma 5.3 (A lower bound for inverse Frobenius estimation), corrected: `n ≥ 1`** (Dereziński, Mahoney, Meyer, Musco, *From smoothed analysis to backward error: The power of adaptive perturbations*, manuscript of 3 Nov 2026, sha256 9575cd20…,
Lemma 5.3, p.11).

Let `A ∈ ℝ^{n×n}` have iid `N(0,1)` entries, let `Δ ∈ ℝ^{n×n}` be independent of `A` with
`‖Δ‖₂ ≤ √n/3` almost surely, and set `Â := A + Δ`. There is a universal constant `ρ > 0` such that
every randomized estimator `F̂` using at most `t ≤ 3n/32` paired matvecs with `Â` satisfies
`F̂ ∉ [½‖Â⁻¹‖_F², 2‖Â⁻¹‖_F²]` with probability at least `ρ`.

**Formalization Note** `ρ` is chosen before `n`, the law `ν` of `Δ`, `t` and the estimator. An
estimator is a randomized adaptive paired matvec algorithm with no input (`Unit`), real output and
exactly `t` steps (an estimator with fewer steps ignores its last answers), with a seed law `μ`
independent of `(A, Δ)`; the probability is over `μ ⊗ gaussianMatrix n n ⊗ ν`. `‖·‖_F²` is the
published `frobSq`, and `Â⁻¹` is Mathlib's total inverse. The hypothesis `n ≥ 1` is a correction:
at `n = 0`, `Â` is the empty matrix, `‖Â⁻¹‖_F² = 0`, and the estimator `F̂ = 0` always lies in
`[0, 0]`. -/
theorem lemma_5_3 :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ (ν : Measure (Fin n → Fin n → ℝ)) [IsProbabilityMeasure ν],
        (∀ᵐ Δ ∂ν, specNorm (Matrix.of Δ) ≤ Real.sqrt n / 3) →
        ∀ (t : ℕ), (t : ℝ) ≤ 3 * n / 32 →
        ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (alg : PairedMatvecAlg n t Unit Ω ℝ),
          ENNReal.ofReal ρ ≤ (μ.prod ((gaussianMatrix n n).prod ν))
            {q | alg.run (Matrix.of q.2.1 + Matrix.of q.2.2) () q.1 <
                  frobSq ((Matrix.of q.2.1 + Matrix.of q.2.2)⁻¹) / 2 ∨
                2 * frobSq ((Matrix.of q.2.1 + Matrix.of q.2.2)⁻¹) <
                  alg.run (Matrix.of q.2.1 + Matrix.of q.2.2) () q.1} := by sorry

end SmoothBerr
