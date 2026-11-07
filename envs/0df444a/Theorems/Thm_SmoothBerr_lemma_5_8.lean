-- Prove2me | Theorems.Thm_SmoothBerr_lemma_5_8
-- name    : SmoothBerr.lemma_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:28:16.391233+00:00
-- url     : https://prove2.me/theorems/d27b9f77-f9c4-46b4-a117-8681a0832c60
-- title:
--   Lemma 5.8 — inverse spectral tail: $\mathbb E\sum_{j\le n-2}\sigma_j(\hat A)^{-2}\le n-2$
-- statement:
--   Let $n\ge8$, let $A\in\mathbb R^{n\times n}$ have iid $\mathcal N(0,1)$ entries, let $\Delta$ be independent of $A$ with $\|\Delta\|_2\le\sqrt n/2$ almost surely, and set $\hat A=A+\Delta$. With $\sigma_1(\hat A)\ge\dots\ge\sigma_n(\hat A)$ the singular values in decreasing order,
--   $$
--   \mathbb E\Big[\sum_{j=1}^{n-2}\sigma_j(\hat A)^{-2}\Big]\le n-2 .
--   $$
--   Leaving out the two smallest singular values, the inverse singular values have a bounded average; this controls all but two directions in the proof of Lemma 5.5.
--
--   **Formalization Note** The terms $\sigma_j^{-2}$ are computed in $[0,\infty]$ (so a vanishing singular value contributes $\infty$), and the expectation is a lower Lebesgue integral.
--
--   Differences from the source:
--   - reading: Â = A + Δ "defined as in Theorem 4.2" → n ≥ 8, A with law gaussianMatrix n n, Δ with an arbitrary probability law ν such that ‖Δ‖₂ ≤ √n/2 ν-a.s., and the product law gaussianMatrix n n ⊗ ν; reason: the setting of Theorem 4.2 (p.5): Δ independent of A with ‖Δ‖₂ ≤ √n/2 almost surely
--   - encoding: σ_j(Â), j = 1, …, n − 2 (1-based, decreasing) → singVal Â j for 0-based j < n − 2; reason: same n − 2 largest singular values
--   - encoding: E[Σ σ_j(Â)^{−2}] → lower Lebesgue integral of Σ (ENNReal.ofReal σ_j)⁻¹ ^ 2, with value ∞ when σ_j = 0; reason: same value for a nonnegative integrand; no junk value
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), Lemma 5.8, Eq. (16), p.15

import Mathlib
import Definitions.Def_GaussianMatrix_basic
import Definitions.Def_SmoothBerr_singVal

open MeasureTheory ProbabilityTheory Matrix GaussianMatrix
open scoped ENNReal

namespace SmoothBerr

/-- **Lemma 5.8 (Inverse spectral tail)** (Dereziński, Mahoney, Meyer, Musco, *From smoothed analysis to backward error: The power of adaptive perturbations*, manuscript of 3 Nov 2026, sha256 9575cd20…, Lemma 5.8, Eq. (16), p.15).

Let `Â = A + Δ` be as in Theorem 4.2: `n ≥ 8`, `A ∈ ℝ^{n×n}` with iid `N(0,1)` entries, `Δ`
independent of `A` with `‖Δ‖₂ ≤ √n/2` almost surely. Then
`E[∑_{j=1}^{n−2} σ_j(Â)^{−2}] ≤ n − 2`,
where `σ_1(Â) ≥ … ≥ σ_n(Â)` are the singular values in decreasing order.

**Formalization Note** `singVal` is 0-based, so the paper's `j = 1, …, n − 2` are the indices
`0, …, n − 3`: the sum runs over the `n − 2` largest singular values. Each term is `σ_j^{−2}`
computed in `[0, ∞]` (`(ENNReal.ofReal σ_j)⁻¹ ^ 2`, which is `∞` when `σ_j = 0`), and the
expectation is a lower Lebesgue integral, so no junk value can make the bound hold. Independence
of `Δ` and `A` is the product measure `gaussianMatrix n n ⊗ ν`. -/
theorem lemma_5_8 (n : ℕ) (hn : 8 ≤ n) (ν : Measure (Fin n → Fin n → ℝ)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ Δ ∂ν, specNorm (Matrix.of Δ) ≤ Real.sqrt n / 2) :
    ∫⁻ q, ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < n - 2),
        (ENNReal.ofReal (singVal (Matrix.of q.1 + Matrix.of q.2) j))⁻¹ ^ 2
        ∂((gaussianMatrix n n).prod ν) ≤
      ENNReal.ofReal ((n : ℝ) - 2) := by sorry

end SmoothBerr
