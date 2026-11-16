-- Prove2me | Theorems.Thm_RankingQueryCost_Joint_Supplement_lemma_5_1
-- name    : RankingQueryCost.Joint.Supplement.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:49:43.32495+00:00
-- url     : https://prove2.me/theorems/215ed683-a82a-4c69-884a-2765818a3297
-- title:
--   Lemma 5.1 — Obtuse rank displacements
-- statement:
--   Let $k\ge1$ fixed-support worlds share one complete table $T_0$ and have compatible ranks $r^j=p+d^j$. Assume $\langle d^i,d^j\rangle\le0$ for $i\ne j$ and $\|d^j\|^2\ge S$ for every $j$. Put $m=\lceil3k/4\rceil$. Then
--
--   $$M_{\rm act}(n,s)\ge(1-1/m)S,\qquad\rho_s(T_0)\ge(1-1/k)S.$$
--
--   The center $p$ is an arbitrary real vector. The statement applies to every finite $n$ and budget $s$, without the main theorems' admissibility restriction. It controls actual randomized estimation as well as the public radius. Compatibility with the complete table exactly expresses existence of the fixed-support worlds.
--
--   Differences from the source:
--   - encoding: n labelled objects and ranks 0 through n−1 → Fin n labels and Rank n permutations; reason: a bijective encoding preserving every instance and the full continuous output space Q
--   - encoding: nonnegative real full-information thresholds and radii → extended nonnegative real operational extrema, with explicit finiteness before real-valued limits; reason: prevents empty or unbounded real infimum defaults; compact Q and finite tables recover the stated real extrema
--   - encoding: k worlds and m=ceil(3k/4) → k≥1 and m=(3*k+3)/4 in natural arithmetic; reason: k≥1 is the implicit nondegeneracy of both reciprocals, and the integer formula is exactly the ceiling
--   - generalization: the standing admissible comparison domain of §2.1 → every finite ambient n and natural budget s, without Admissible n s; reason: the common-table packing argument depends only on compatibility and the displacement hypotheses; restricting to admissible instances recovers the complete source claim
-- source:
--   Chaoqiang Fu, Yifan Su, Daofeng Li, STOC 2027 submission #812 (October 2026), Lemma 5.1, p. 25, PDF p. 26

import Definitions.Def_RankingQueryCost_Joint_Supplement_Radius
import Definitions.Def_RankingQueryCost_Joint_Supplement_ActualThreshold

set_option autoImplicit false

namespace RankingQueryCost.Joint.Supplement

/-- Lemma 5.1, printed p. 25 / PDF 26. The nonempty candidate family is
implicit in the paper's divisions by k and ceil(3k/4). No admissible-domain
restriction is imposed on n or s in this pure packing result. -/
theorem lemma_5_1 (n s k : ℕ) (hk : 1 ≤ k) (T : Tournament n)
    (r : Fin k → Rank n) (p : Fin n → ℝ) (d : Fin k → Fin n → ℝ) (S : ℝ)
    (hworlds : ∀ j, r j ∈ compatible s (completeTranscript T))
    (hranks : ∀ j i, rankVector (r j) i = p i + d j i)
    (hobtuse : ∀ i j, i ≠ j → ∑ v, d i v * d j v ≤ 0)
    (hnorm : ∀ j, S ≤ ∑ v, (d j v) ^ 2) :
    let m : ℕ := (3 * k + 3) / 4
    ENNReal.ofReal ((1 - 1 / (m : ℝ)) * S) ≤ actualThreshold n s ∧
    ENNReal.ofReal ((1 - 1 / (k : ℝ)) * S) ≤ radius s T := by sorry

end RankingQueryCost.Joint.Supplement
