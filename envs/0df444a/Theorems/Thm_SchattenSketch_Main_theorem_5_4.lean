-- Prove2me | Theorems.Thm_SchattenSketch_Main_theorem_5_4
-- name    : SchattenSketch.Main.theorem_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:57:53.829465+00:00
-- url     : https://prove2.me/theorems/ee27e6b1-aea2-4873-beeb-3306bec7e5de
-- title:
--   Theorem 5.4 — Gaussian injective-cycle bound [KV17]: with probability $1-\zeta$, $\hat p_j$ estimates $\mathrm{tr}(\Sigma^j)$ within relative error $f(j)\zeta^{-1/2}\max\{\cdot\}$
-- statement:
--   Let $2\le j\le s$ and $0<\zeta<1$, and let $z_1,\dots,z_s\in\mathbb R^n$ be independent $N(0,\Sigma)$ vectors for a positive semidefinite $\Sigma$. Then the injective cycle statistic $\hat p_j$ of (5.29) satisfies, with probability at least $1-\zeta$,
--   $$\bigl|\hat p_j-\mathrm{tr}(\Sigma^j)\bigr|\le\frac{f(j)}{\sqrt\zeta}\max\Bigl\{\frac{n^{j/2-1}}{s^{j/2}},\ \frac{n^{1/4-1/(2j)}}{\sqrt s},\ \frac1{\sqrt s}\Bigr\}\,\mathrm{tr}(\Sigma^j),\qquad f(j)=2^{6j}j^{3j}3^{j/2}.$$
--
--   The paper states this as "Chebyshev's inequality at failure probability $\zeta$ gives relative error at most" the displayed factor; the error is relative to the target $\mathrm{tr}(\Sigma^j)=\mathbb E\hat p_j$ (5.30). It drives the estimate of the spectral moments $\mu_j$ of a well-spread tail in §5.6.
--
--   **Formalization Note.** $\Sigma=C^\top C$ for an arbitrary real $C\in\mathbb R^{n\times n}$ (every positive semidefinite $\Sigma$ arises, e.g. $C=\Sigma^{1/2}$), and the samples are the rows of $gC$ with $g$ distributed as the published `gaussianMatrix s n`: the $a$-th row is $C^\top g_a\sim N(0,C^\top C)$. Powers with real exponents are `Real.rpow`.
--
--   Differences from the source:
--   - reading: Chebyshev's inequality at failure probability ζ gives relative error at most E → P{|p̂_j − tr(Σ^j)| ≤ E · tr(Σ^j)} ≥ 1 − ζ; reason: relative to the target tr(Σ^j) = E p̂_j of (5.30), as (D.5) uses it
--   - encoding: rows z_a i.i.d. N(0, Σ), Σ positive semidefinite → z = g C with g ∼ gaussianMatrix s n, Σ = CᵀC for arbitrary C ∈ R^{n×n}; reason: C^T g_a ∼ N(0, CᵀC), and every PSD Σ is CᵀC (C = Σ^{1/2})
--   - encoding: n^{j/2−1}, s^{j/2}, n^{1/4−1/(2j)}, 3^{j/2} → real powers (rpow); reason: same values
-- source:
--   Lin F. Yang, Near-Optimal Bounds for Sketching the Schatten Norms, arXiv:2608.22247 (held version, sha256 c29a210a…), p. 30, Theorem 5.4, (5.31) ([KV17, Theorem 1 and Proposition 4]; statistic p. 29, (5.29)–(5.30))

import Mathlib
import Definitions.Def_GaussianMatrix_basic
import Definitions.Def_SchattenSketch_Main_Cycle

open MeasureTheory GaussianMatrix

namespace SchattenSketch.Main

/-- Theorem 5.4 (Gaussian injective-cycle variance bound [KV17]; Yang, p. 30). Let `2 ≤ j ≤ s`,
`0 < ζ < 1`, and let `z₁, …, z_s` be i.i.d. `N(0, Σ)` vectors in `ℝⁿ` for a positive semidefinite
`Σ = CᵀC` (here `z_a = Cᵀ g_a`, the `a`-th row of `g C`, with `g` an `s × n` standard Gaussian
matrix). With probability at least `1 - ζ` the injective cycle statistic `p̂_j` of (5.29) estimates
`tr(Σ^j)` within relative error
`(f(j)/√ζ) max{n^{j/2-1}/s^{j/2}, n^{1/4-1/(2j)}/√s, 1/√s}`, `f(j) = 2^{6j} j^{3j} 3^{j/2}`. -/
theorem theorem_5_4 (n s j : ℕ) (hj : 2 ≤ j) (hjs : j ≤ s) (ζ : ℝ) (hζ : 0 < ζ) (hζ1 : ζ < 1)
    (C : Matrix (Fin n) (Fin n) ℝ) :
    let Sig : Matrix (Fin n) (Fin n) ℝ := C.transpose * C
    let f : ℝ := (2 : ℝ) ^ (6 * j) * (j : ℝ) ^ (3 * j) * (3 : ℝ) ^ ((j : ℝ) / 2)
    let err : ℝ := f / Real.sqrt ζ *
      max (max ((n : ℝ) ^ ((j : ℝ) / 2 - 1) / (s : ℝ) ^ ((j : ℝ) / 2))
        ((n : ℝ) ^ ((1 : ℝ) / 4 - 1 / (2 * (j : ℝ))) / Real.sqrt s)) (1 / Real.sqrt s)
    ENNReal.ofReal (1 - ζ) ≤
      gaussianMatrix s n {g |
        |cycleStat (Matrix.of g * C) j - (Sig ^ j).trace| ≤ err * (Sig ^ j).trace} := by sorry

end SchattenSketch.Main
