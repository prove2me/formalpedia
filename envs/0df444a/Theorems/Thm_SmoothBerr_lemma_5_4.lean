-- Prove2me | Theorems.Thm_SmoothBerr_lemma_5_4
-- name    : SmoothBerr.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:27:30.43672+00:00
-- url     : https://prove2.me/theorems/97f165c1-e6f8-48ae-9bfb-edd5f7460aae
-- title:
--   Lemma 5.4 — small-ball lower bound: $\mathbb P[\|\hat A^{-1}v\|_2\ge t]\ge c/t$
-- statement:
--   Let $n\ge8$, let $A\in\mathbb R^{n\times n}$ have iid $\mathcal N(0,1)$ entries, let $\Delta$ be independent of $A$ with $\|\Delta\|_2\le\sqrt n/2$ almost surely, and set $\hat A=A+\Delta$ (the setting of Theorem 4.2). There is an absolute constant $c>0$ such that for every deterministic unit vector $v\in\mathbb R^n$ and every $t\ge1$,
--   $$
--   \mathbb P\big[\|\hat A^{-1}v\|_2\ge t\big]\ge\frac ct .
--   $$
--   In every fixed direction the inverse of a perturbed Gaussian matrix has a heavy tail; this is one of the two estimates combined in the proof of Theorem 4.2.
--
--   **Formalization Note** The level $t$ is named $\tau$ in Lean ($t$ denotes the number of queries elsewhere in the mission). The constant $c$ is chosen before $n$, the law of $\Delta$, $v$ and $\tau$.
--
--   Differences from the source:
--   - reading: Â = A + Δ "defined as in Theorem 4.2" → n ≥ 8, A with law gaussianMatrix n n, Δ with an arbitrary probability law ν such that ‖Δ‖₂ ≤ √n/2 ν-a.s., and the product law gaussianMatrix n n ⊗ ν; reason: the setting of Theorem 4.2 (p.5): Δ independent of A with ‖Δ‖₂ ≤ √n/2 almost surely
--   - encoding: an absolute constant c > 0 → ∃ c > 0 quantified before n, ν, v and t; reason: §3, p.4: universal constants do not depend on the instance
--   - encoding: Â⁻¹ → Mathlib's total inverse (0 on singular Â); reason: Â is singular only on a null event (A has a density, independent of Δ); the event is empty there
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), Lemma 5.4, Eq. (11), p.13

import Mathlib
import Definitions.Def_GaussianMatrix_basic
import Definitions.Def_ApproxVI_euclNorm

open MeasureTheory ProbabilityTheory Matrix GaussianMatrix

namespace SmoothBerr

/-- **Lemma 5.4 (Lower bound)** (Dereziński, Mahoney, Meyer, Musco, *From smoothed analysis to backward error: The power of adaptive perturbations*, manuscript of 3 Nov 2026, sha256 9575cd20…, Lemma 5.4, Eq. (11), p.13).

Let `Â = A + Δ` be as in Theorem 4.2: `n ≥ 8`, `A ∈ ℝ^{n×n}` with iid `N(0,1)` entries, `Δ`
independent of `A` with `‖Δ‖₂ ≤ √n/2` almost surely. There is an absolute constant `c > 0` such
that for every deterministic unit vector `v ∈ ℝⁿ` and every `t ≥ 1`,
`P[‖Â⁻¹v‖₂ ≥ t] ≥ c/t`.

**Formalization Note** The constant `c` is chosen before `n`, the law `ν` of `Δ`, `v` and `t`.
Independence of `Δ` and `A` is the product measure `gaussianMatrix n n ⊗ ν`. The paper's level `t`
is named `τ` here (`t` is the number of queries elsewhere in the mission). `‖·‖₂` on vectors is
the published `ApproxVI.euclNorm`; `Â⁻¹` is Mathlib's total inverse (`0` on the null event that `Â` is singular). -/
theorem lemma_5_4 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (n : ℕ), 8 ≤ n → ∀ (ν : Measure (Fin n → Fin n → ℝ)) [IsProbabilityMeasure ν],
        (∀ᵐ Δ ∂ν, specNorm (Matrix.of Δ) ≤ Real.sqrt n / 2) →
        ∀ v : Fin n → ℝ, v ⬝ᵥ v = 1 → ∀ τ : ℝ, 1 ≤ τ →
          ENNReal.ofReal (c / τ) ≤ ((gaussianMatrix n n).prod ν)
            {q | τ ≤ ApproxVI.euclNorm ((Matrix.of q.1 + Matrix.of q.2)⁻¹ *ᵥ v)} := by sorry

end SmoothBerr
