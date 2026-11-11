-- Prove2me | Theorems.Thm_ParallelMatroidBasis_Main_corollary_3_16
-- name    : ParallelMatroidBasis.Main.corollary_3_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:45:55.260618+00:00
-- url     : https://prove2.me/theorems/42586929-2dd0-4f47-9b78-d5666ab66da7
-- title:
--   Corollary 3.16 — KL contraction of the up operator: $d_{KL}(U_{m\to i}\mu\|U_i)\le\frac{n-i}{n-m}d_{KL}(\mu\|U_m)$
-- statement:
--   Let $0\le m<i\le n$ be integers and let $\mu$ be any distribution over $\binom{[n]}{m}$. Let $U_{m\to i}$ be $i-m$ consecutive applications of the up operator, which replaces each set $T$ by a uniformly random superset with one more element. Then
--   $$d_{KL}\big(U_{m\to i}(\mu)\,\big\|\,U_i\big)\ \le\ \frac{n-i}{n-m}\; d_{KL}(\mu\,\|\,U_m).$$
--
--   Growing a random set from size $m$ to size $i$ brings its law closer to uniform by the factor $(n-i)/(n-m)$. In Theorem 4.1 this bounds the divergence of the law of a random superset of a uniformly random member of a dense family.
--
--   Differences from the source:
--   - encoding: distributions over ([n] k) and base-2 KL divergence → `PMF (Finset (Fin n))` with support in the k-element sets, `klBits` = Mathlib's klDiv of the induced measures divided by ln 2, and an `ENNReal` product on the right-hand side; reason: on the discrete σ-algebra of `Finset (Fin n)` this is the finite sum of Definition 3.9; both sides are finite because U_k has full support on the k-sets
-- source:
--   Aaron Putterman, Sanjeev Khanna, Junkai Song, STOC 2027 submission #589 (October 2026), A Near-Optimal Parallel Algorithm for Finding Matroid Bases, PDF sha256 71ee2ac010ac681077fc3191139efe918fa4a9b8c6dad648fac2ec33016764d6, Corollary 3.16, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_ParallelMatroidBasis_Main_KL

noncomputable section
open Classical MeasureTheory

namespace ParallelMatroidBasis.Main

/-- Corollary 3.16, PDF p.14 (printed p.12). For integers `0 ≤ m < i ≤ n` and every distribution
`μ` over `([n] choose m)`, `d_KL(U_{m→i}(μ) ‖ U_i) ≤ ((n−i)/(n−m)) · d_KL(μ ‖ U_m)`, where
`U_{m→i}` is `i − m` consecutive up steps. -/
theorem corollary_3_16 (n m i : ℕ) (hmi : m < i) (hin : i ≤ n) (μ : PMF (Finset (Fin n)))
    (hμ : IsDistOn n m μ) :
    klBits (upOp n (i - m) μ).toMeasure (uniformK n i).toMeasure ≤
      ENNReal.ofReal (((n : ℝ) - i) / ((n : ℝ) - m)) *
        klBits μ.toMeasure (uniformK n m).toMeasure := by sorry

end ParallelMatroidBasis.Main
