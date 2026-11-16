-- Prove2me | Theorems.Thm_UnknownCovDP_General_Supplement_theorem_3_4
-- name    : UnknownCovDP.General.Supplement.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:47:26.501594+00:00
-- url     : https://prove2.me/theorems/5382787f-a846-4d40-af3b-5a779a398d3d
-- title:
--   Theorem 3.4 — lower bound for private selection of large-variance coordinates
-- statement:
--   Let $\mathcal P_{\mathrm{diag}}(d)$ be the prior under which $\Sigma=\mathrm{Diag}(\sigma_1^2,\dots,\sigma_d^2)$ with the $\sigma_i^2$ i.i.d. $\mathrm{inv}\chi^2(1,1)$. A randomized algorithm $\mathcal M$ that maps a dataset of $n$ points of $\mathbb R^d$ to $s\in\{0,1\}^d$ is a **$(k,\ell)$-selection mechanism for $\mathcal P_{\mathrm{diag}}$ with sample complexity $n$** if every output satisfies $\sum_j s_j\le\ell$, and, with $\Sigma$ from $\mathcal P_{\mathrm{diag}}$, $X\sim N(0,\Sigma)^{\otimes n}$ and $\pi$ ordering the variances decreasingly,
--   $$\Pr\Bigl[\sum_{j=1}^k s_{\pi(j)}\ge \tfrac k4\Bigr]\ge\tfrac13 .$$
--
--   There are absolute constants $C,c>0$ such that for all $d,k,n\in\mathbb N$ with $n\ge1$ and
--   $$C\max\{n^2\log n,\ \log d\}\le k\le c\,d,$$
--   every $(k,\ell)$-selection mechanism for $\mathcal P_{\mathrm{diag}}$ with sample complexity $n$ that is $(1,c/n)$-differentially private has
--   $$\ell\ \ge\ \frac{d}{C\log d}.$$
--
--   A private mechanism that reliably finds a constant fraction of the $k$ largest-variance coordinates must therefore select almost all $d$ coordinates. Combined with a reduction from mean estimation, this gives Theorem 3.2.
--
--   Differences from the source:
--   - encoding: d, k, n ∈ ℕ with c/n in the DP parameter → 1 ≤ n; reason: c/n is undefined at n = 0; the base mission's accepted encoding
--   - reading: ℓ ≥ d/C log(d) → d / (C * log d) ≤ ℓ; reason: the other parse (d/C)·log d is false: the constant all-ones mechanism is a (1,0)-DP (k, d)-selection mechanism, so ℓ = d is always achievable and d ≥ (d/C) log d fails for large d; the proof of Theorem 3.2 (p. 17) also uses ℓ ≥ d/(C log d)
--   - encoding: d/(C log d), undefined at d = 1 → real division with x/0 = 0, so the bound is 0 at d ≤ 1; reason: Lean convention; no hypothesis is added
--   - encoding: s ∈ {0,1}^d, π the permutation ordering the variances decreasingly → s : Fin d → Bool; {π(1),…,π(k)} = topK k Σ, ties broken by the smaller index; reason: ties among the σ_j² have probability zero under P_diag
--   - encoding: Boundedness Σ_j s_j ≤ ℓ of the output → for every dataset X, M X {s | ℓ < Σ_j s_j} = 0; reason: the output satisfies the bound for every input and almost every coin
-- source:
--   Gaucher, Linder, Smith, Ullman, Zakynthinou, Dimension-Free Private Mean Estimation is Impossible Without the Covariance, STOC 2027 submission #573 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/573.pdf, Theorem 3.4, printed p. 17 (PDF p. 18); Definition 3.3, same page; prior eq. (9), printed p. 16 (PDF p. 17)

import Mathlib
import Definitions.Def_UnknownCovDP_General_Supplement_DiagPrior

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace UnknownCovDP.General.Supplement

/-- Theorem 3.4 (Lower bound for private selection), printed p. 17, PDF p. 18. There are
`C, c > 0` such that for all `d, k, n` with `C max{n² log n, log d} ≤ k ≤ cd`, every
`(k, ℓ)`-selection mechanism for `P_diag` with sample complexity `n` that is `(1, c/n)`-DP has
`ℓ ≥ d/(C log d)`. `n ≥ 1` because `c/n` is undefined at `n = 0`. At `d = 1` the bound is `0` in
Lean. -/
theorem theorem_3_4 :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (d k n : ℕ), 1 ≤ n →
      C * max ((n : ℝ) ^ 2 * Real.log n) (Real.log d) ≤ k → (k : ℝ) ≤ c * d →
      ∀ (ℓ : ℕ) (M : SelMech d n), IsMarkovKernel M →
        IsSelectionMechanism k ℓ M →
        PrivRobustStat.IsApproxDP (fun X => M X) 1 (c / n) →
        (d : ℝ) / (C * Real.log d) ≤ ℓ := by sorry

end UnknownCovDP.General.Supplement
