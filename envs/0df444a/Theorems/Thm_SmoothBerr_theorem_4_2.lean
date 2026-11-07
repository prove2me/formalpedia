-- Prove2me | Theorems.Thm_SmoothBerr_theorem_4_2
-- name    : SmoothBerr.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:27:39.705199+00:00
-- url     : https://prove2.me/theorems/3503e69e-286c-45f9-ada8-98029a04f090
-- title:
--   Theorem 4.2 — perturbed Gaussian matrix: $\sigma_{\min}(\hat A)\le 1/(s\sqrt n)$ with probability $\gtrsim 1/s^2$
-- statement:
--   Let $n\ge8$, let $A\in\mathbb R^{n\times n}$ have iid $\mathcal N(0,1)$ entries, let $\Delta\in\mathbb R^{n\times n}$ be independent of $A$ with $\|\Delta\|_2\le\sqrt n/2$ almost surely, and set $\hat A:=A+\Delta$. There is a universal constant $c>0$ such that for all $s\ge1$,
--   $$
--   \mathbb P\Big[\sigma_{\min}(\hat A)\le\frac1{s\sqrt n}\Big]\ge\frac c{s^2}.
--   $$
--   No oblivious perturbation of size $O(\sqrt n)$ can make a Gaussian matrix well conditioned: its condition number stays of order $n$ with constant probability. This matches, in the opposite direction, the smoothed upper bound of Sankar, Spielman and Teng.
--
--   **Formalization Note** $\sigma_{\min}$ is the published `sMin` and $\|\cdot\|_2$ the published `specNorm`.
--
--   Differences from the source:
--   - encoding: with prob. ≳ 1/s² → ∃ c > 0, chosen before n, ν and s, with probability ≥ c/s²; reason: §3, p.4: ≳ hides a universal constant
--   - encoding: Δ independent of A with ‖Δ‖₂ ≤ √n/2 almost surely → any probability law ν with ‖Δ‖₂ ≤ √n/2 ν-a.s., and the product law gaussianMatrix n n ⊗ ν; reason: independence is the product law
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), Theorem 4.2, p.5

import Mathlib
import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory Matrix GaussianMatrix

namespace SmoothBerr

/-- **Theorem 4.2 (The minimum singular value of a perturbed Gaussian matrix)** (Dereziński, Mahoney, Meyer, Musco, *From smoothed analysis to backward error: The power of adaptive perturbations*, manuscript of 3 Nov 2026, sha256 9575cd20…,
Theorem 4.2, p.5).

Let `n ≥ 8`, let `A ∈ ℝ^{n×n}` have iid `N(0,1)` entries, let `Δ ∈ ℝ^{n×n}` be independent of `A`
with `‖Δ‖₂ ≤ √n/2` almost surely, and set `Â := A + Δ`. Then for all `s ≥ 1`,
`σ_min(Â) ≤ 1/(s√n)` with probability `≳ 1/s²`: there is a universal constant `c > 0` with
`P[σ_min(Â) ≤ 1/(s√n)] ≥ c/s²`.

**Formalization Note** "`≳`" hides a universal constant (§3, p.4); `c` is chosen before `n`, the
law `ν` of `Δ` and `s`. Independence is the product measure `gaussianMatrix n n ⊗ ν`. `σ_min` is
the published `sMin` (`inf_{‖x‖₂=1} ‖Âx‖₂`), `‖·‖₂` the published `specNorm`. -/
theorem theorem_4_2 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (n : ℕ), 8 ≤ n → ∀ (ν : Measure (Fin n → Fin n → ℝ)) [IsProbabilityMeasure ν],
        (∀ᵐ Δ ∂ν, specNorm (Matrix.of Δ) ≤ Real.sqrt n / 2) →
        ∀ s : ℝ, 1 ≤ s →
          ENNReal.ofReal (c / s ^ 2) ≤ ((gaussianMatrix n n).prod ν)
            {q | sMin (Matrix.of q.1 + Matrix.of q.2) ≤ 1 / (s * Real.sqrt n)} := by sorry

end SmoothBerr
