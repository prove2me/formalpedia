-- Prove2me | Theorems.Thm_RankingQueryCost_Joint_Supplement_proposition_5_2
-- name    : RankingQueryCost.Joint.Supplement.proposition_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:50:33.02839+00:00
-- url     : https://prove2.me/theorems/73337202-8ff1-4fe3-9f12-9af4931626b8
-- title:
--   Proposition 5.2 — Finite clean-table bounds
-- statement:
--   Let $1\le s<n$, let $T_0$ be the clean comparison table of the identity ranks $p_i=i$, and set $U=s(s+1)$, $m=n-s$, $k=\lceil3m/4\rceil$. Then
--
--   $$M_{\rm act}(n,s)\ge(1-1/k)U,\qquad\rho_s(T_0)\ge(1-1/m)U.$$
--
--   For $n\ge6$ the refined bounds are
--
--   $$U-\frac{3U^2}{(n-s)(n-s+1)(n-s+2)}\le\rho_s(T_0)\le U-\frac{3U^2}{n(n^2-1)}.$$
--
--   Consequently, along every sequence $n\to\infty$ with $1\le s<n$ and $s/n\to0$,
--
--   $$\frac{(U-\rho_s(T_0))n^3}{U^2}\longrightarrow3.$$
--
--   For every $n\ge6$, $\rho_1(T_0)=2-12/[n(n^2-1)]$. All quantities converted to reals are explicitly finite. These finite and asymptotic bounds concern this particular clean-table compatible set, and supply the sparse part of Theorem 2.1.
--
--   Differences from the source:
--   - encoding: n labelled objects and ranks 0 through n−1 → Fin n labels and Rank n permutations; reason: a bijective encoding preserving every instance and the full continuous output space Q
--   - encoding: nonnegative real full-information thresholds and radii → extended nonnegative real operational extrema, with explicit finiteness before real-valued limits; reason: prevents empty or unbounded real infimum defaults; compact Q and finite tables recover the stated real extrema
--   - encoding: rho=U−(3+o(1))*U²/n³ for s=o(n) → the normalized deficit tends to 3 along every n→infinity, 1≤s<n, s/n→0 sequence; reason: an equivalent ratio-limit statement with U=s(s+1)>0
-- source:
--   Chaoqiang Fu, Yifan Su, Daofeng Li, STOC 2027 submission #812 (October 2026), Proposition 5.2, p. 26, PDF p. 27

import Definitions.Def_RankingQueryCost_Joint_Supplement_Radius
import Definitions.Def_RankingQueryCost_Joint_Supplement_ActualThreshold
import Definitions.Def_RankingQueryCost_Joint_Scale

set_option autoImplicit false

namespace RankingQueryCost.Joint.Supplement

/-- Proposition 5.2, printed p. 26 / PDF 27, all finite and limit clauses.
The clean table is constructed from the identity order, not a free table.
Finiteness accompanies every toReal used in the asymptotic and exact clauses. -/
theorem proposition_5_2 :
    (∀ n s : ℕ, 1 ≤ s → s < n →
      let m := n - s
      let k := (3 * m + 3) / 4
      let U : ℝ := (s : ℝ) * (s + 1)
      let T : Tournament n := truthful (Equiv.refl _)
      actualThreshold n s ≠ ⊤ ∧ radius s T ≠ ⊤ ∧
      ENNReal.ofReal ((1 - 1 / (k : ℝ)) * U) ≤ actualThreshold n s ∧
      ENNReal.ofReal ((1 - 1 / (m : ℝ)) * U) ≤ radius s T ∧
      (6 ≤ n →
        U - 3 * U ^ 2 / ((m : ℝ) * (m + 1) * (m + 2)) ≤ (radius s T).toReal ∧
        (radius s T).toReal ≤ U - 3 * U ^ 2 / ((n : ℝ) * ((n : ℝ) ^ 2 - 1)))) ∧
    (∀ n : ℕ, 6 ≤ n →
      radius 1 (truthful (Equiv.refl (Fin n))) ≠ ⊤ ∧
      (radius 1 (truthful (Equiv.refl (Fin n)))).toReal =
        2 - 12 / ((n : ℝ) * ((n : ℝ) ^ 2 - 1))) ∧
    ∀ n s : ℕ → ℕ,
      (∀ j, 1 ≤ s j ∧ s j < n j) →
      Filter.Tendsto n Filter.atTop Filter.atTop →
      Filter.Tendsto (fun j => (s j : ℝ) / (n j : ℝ)) Filter.atTop (nhds 0) →
      Filter.Tendsto (fun j =>
        let U : ℝ := (s j : ℝ) * (s j + 1)
        (U - (radius (s j) (truthful (Equiv.refl (Fin (n j))))).toReal) *
          (n j : ℝ) ^ 3 / U ^ 2) Filter.atTop (nhds 3) := by sorry

end RankingQueryCost.Joint.Supplement
