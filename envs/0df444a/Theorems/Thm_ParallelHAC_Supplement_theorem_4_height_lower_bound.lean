-- Prove2me | Theorems.Thm_ParallelHAC_Supplement_theorem_4_height_lower_bound
-- name    : ParallelHAC.Supplement.theorem_4_height_lower_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:34:41.086075+00:00
-- url     : https://prove2.me/theorems/8e65c5d8-784e-44aa-953b-5870e233837a
-- title:
--   Theorem 4 — for $k=\omega(\log\log n)$ every 1.1-approximate centroid HAC can have height $\omega(\log^\alpha n)$
-- statement:
--   Let $k:\mathbb N\to\mathbb N$ satisfy $k(n)=\omega(\log\log n)$, that is $k(n)/\log\log n\to\infty$. Then there are point sets $P_n\subseteq\mathbb R^{k(n)}$, one for each $n$, and a constant $\rho>0$ such that for all sufficiently large $n$:
--   1. $|P_n|=n$;
--   2. the aspect ratio of $(P_n,d_{\mathrm{cen}})$ is at most $\rho n^\rho$ (poly($n$) aspect ratio);
--
--   and every $1.1$-approximate HAC with $d_{\mathrm{cen}}$ on $P_n$, under any tie-breaking, has dendrogram height $\omega(\log^\alpha n)$ for every constant $\alpha>0$: for every $\alpha>0$ and every $M$, for all sufficiently large $n$, every such run $R$ satisfies
--   $$\mathrm{height}(R)\ge M(\log n)^\alpha .$$
--
--   The theorem shows that the $\mathrm{poly}(\log n)$ height bound of Theorem 3 cannot extend beyond dimension $O(\log\log n)$, even for centroid linkage.
--
--   **Formalization Note** Runs, height and aspect ratio are the base mission's `ParallelHAC.HACRun`, `HACRun.height` (maximum depth of a leaf) and `AspectRatioLE`; $1.1$ is $11/10$.
--
--   Differences from the source:
--   - encoding: k = ω(log log n) → k : ℕ → ℕ with Tendsto (fun n => (k n : ℝ) / Real.log (Real.log n)) atTop atTop; reason: the definition of ω(·); the base of the logarithms only changes a constant factor
--   - reading: a family of n-point sets, one for each n, with poly(n) aspect ratio → P : (n : ℕ) → Finset (EuclideanSpace ℝ (Fin (k n))) and one ρ > 0 with |P n| = n and AspectRatioLE (P n) d_cen ρ for all sufficiently large n; reason: for small n with k(n) = 0 the space ℝ^0 has one point, so no n-point set exists there; the statement is asymptotic, and only large n matter
--   - encoding: any 1.1-approximate HAC has dendrogram height ω(log^α n) for any constant α > 0 → ∀ α > 0, ∀ M, ∀ᶠ n, ∀ R : HACRun (P n) d_cen (11/10), M · (log n)^α ≤ R.height; reason: the definition of ω(·), uniformly over every run (every tie-breaking)
--   - reading: aspect ratio max_{u,v} d(u,v) / min_{u,v} d(u,v) → AspectRatioLE: positive distances between distinct points and d(u,v) ≤ ρ n^ρ d(w,x) for distinct pairs; reason: the base mission's reading: the extrema range over distinct pairs (at u = v the ratio is undefined)
-- source:
--   Bateni, Dhulipala, Fletcher, Gowda, Hershkowitz, Jayaram, Łącki, Parallel Hierarchical Agglomerative Clustering in Low Dimensions, arXiv:2507.20047 (sha256 a21061c8…), §2.3, Theorem 4, p.10 (PDF p.13); restated p.50 (PDF p.53), proof §7, pp.50–52 (PDF pp.53–55)

import Mathlib
import Definitions.Def_ParallelHAC_AspectRatioLE
import Definitions.Def_ParallelHAC_HACRun
import Definitions.Def_ParallelHAC_HACRun_height
import Definitions.Def_ParallelHAC_Supplement_centroidLinkage

namespace ParallelHAC.Supplement

open Filter

/-- **Theorem 4** (p.10): suppose `k = ω(log log n)`. Then there is a family of `n`-point sets
`P_n ⊆ ℝ^{k(n)}` (one for each `n`) with `poly(n)` aspect ratio such that every 1.1-approximate
HAC with `d_cen` has dendrogram height `ω(log^α n)` for every constant `α > 0`.

Formally: for every `k : ℕ → ℕ` with `k(n) / log log n → ∞` there are sets
`P_n ⊆ EuclideanSpace ℝ (Fin (k n))` and one `ρ > 0` such that, for all large `n`, `|P_n| = n` and
the aspect ratio of `(P_n, d_cen)` is at most `ρ n^ρ`; and for every `α > 0` and every `M`, for all
large `n`, every `11/10`-approximate centroid HAC run on `P_n` (any tie-breaking) has height
at least `M (log n)^α`.
Source: arXiv:2507.20047 (sha256 a21061c8…), §2.3, Theorem 4, printed p.10 (PDF p.13); restated
p.50 (PDF p.53), proof §7, pp.50–52.

**Formalization Note.** The size and aspect-ratio conditions are required for all large `n`
(`∀ᶠ n in atTop`): for the small `n` with `k n = 0`, `ℝ^0` has a single point. This changes no
asymptotic statement. The height is the base mission's `HACRun.height`, the maximum depth of a
leaf. -/
theorem theorem_4_height_lower_bound (k : ℕ → ℕ)
    (hk : Tendsto (fun n : ℕ => (k n : ℝ) / Real.log (Real.log n)) atTop atTop) :
    ∃ (P : (n : ℕ) → Finset (EuclideanSpace ℝ (Fin (k n)))) (ρ : ℝ), 0 < ρ ∧
      (∀ᶠ n in atTop, (P n).card = n ∧
        ParallelHAC.AspectRatioLE (P n) (centroidLinkage (k n)) ρ) ∧
      ∀ α : ℝ, 0 < α → ∀ M : ℝ, ∀ᶠ n in atTop,
        ∀ R : ParallelHAC.HACRun (P n) (centroidLinkage (k n)) (11 / 10),
          M * Real.log n ^ α ≤ (R.height : ℝ) := by sorry

end ParallelHAC.Supplement
