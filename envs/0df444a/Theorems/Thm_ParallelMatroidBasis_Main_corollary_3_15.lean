-- Prove2me | Theorems.Thm_ParallelMatroidBasis_Main_corollary_3_15
-- name    : ParallelMatroidBasis.Main.corollary_3_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:46:00.145009+00:00
-- url     : https://prove2.me/theorems/6b65c16b-5557-4f88-ab3c-d89d50700642
-- title:
--   Corollary 3.15 — $d_{KL}(D_{k\to t}\mu\|U_t)\le (t/k)\,d_{KL}(\mu\|U_k)$
-- statement:
--   Let $0\le t<k\le n$ be integers and let $\mu$ be any distribution over $\binom{[n]}{k}$. Let $D_{k\to t}$ be $k-t$ consecutive applications of the down operator. Then
--   $$d_{KL}\big(D_{k\to t}(\mu)\,\big\|\,U_t\big)\ \le\ \frac tk\; d_{KL}(\mu\,\|\,U_k).$$
--
--   Iterating the one-step contraction of Lemma 3.14 telescopes the factors $\prod_{s=t+1}^{k}(1-1/s)=t/k$. Corollary 3.16 transfers this to the up operator by complementation.
--
--   Differences from the source:
--   - encoding: distributions over ([n] k) and base-2 KL divergence → `PMF (Finset (Fin n))` with support in the k-element sets, `klBits` = Mathlib's klDiv of the induced measures divided by ln 2, and an `ENNReal` product on the right-hand side; reason: on the discrete σ-algebra of `Finset (Fin n)` this is the finite sum of Definition 3.9; both sides are finite because U_k has full support on the k-sets
-- source:
--   Aaron Putterman, Sanjeev Khanna, Junkai Song, STOC 2027 submission #589 (October 2026), A Near-Optimal Parallel Algorithm for Finding Matroid Bases, PDF sha256 71ee2ac010ac681077fc3191139efe918fa4a9b8c6dad648fac2ec33016764d6, Corollary 3.15, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_ParallelMatroidBasis_Main_KL

noncomputable section
open Classical MeasureTheory

namespace ParallelMatroidBasis.Main

/-- Corollary 3.15, PDF p.14 (printed p.12). For integers `0 ≤ t < k ≤ n` and every distribution
`μ` over `([n] choose k)`, `d_KL(D_{k→t}(μ) ‖ U_t) ≤ (t/k) · d_KL(μ ‖ U_k)`, where `D_{k→t}` is
`k − t` consecutive down steps. -/
theorem corollary_3_15 (n t k : ℕ) (htk : t < k) (hkn : k ≤ n) (μ : PMF (Finset (Fin n)))
    (hμ : IsDistOn n k μ) :
    klBits (downOp n (k - t) μ).toMeasure (uniformK n t).toMeasure ≤
      ENNReal.ofReal ((t : ℝ) / (k : ℝ)) * klBits μ.toMeasure (uniformK n k).toMeasure := by sorry

end ParallelMatroidBasis.Main
