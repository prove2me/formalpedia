-- Prove2me | Theorems.Thm_ParallelMatroidBasis_Main_lemma_3_14
-- name    : ParallelMatroidBasis.Main.lemma_3_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:45:51.254069+00:00
-- url     : https://prove2.me/theorems/8e53e1ea-c9e1-44b2-acfd-48193a4b5473
-- title:
--   Lemma 3.14 — KL contraction of the down operator: $d_{KL}(D_{k\to k-1}\mu\|U_{k-1})\le(1-1/k)\,d_{KL}(\mu\|U_k)$
-- statement:
--   Let $0<k\le n$ be integers and let $\mu$ be any distribution over $\binom{[n]}{k}$. Write $U_i$ for the uniform distribution on $\binom{[n]}{i}$ and $D_{k\to k-1}$ for the down operator, which replaces each $k$-set by a uniformly random $(k-1)$-subset of it. Then, with base-2 KL divergence,
--   $$d_{KL}\big(D_{k\to k-1}(\mu)\,\big\|\,U_{k-1}\big)\ \le\ \Big(1-\frac1k\Big)\,d_{KL}(\mu\,\|\,U_k).$$
--
--   The down operator contracts relative entropy to the uniform distribution by the factor $1-1/k$. This is the entropic input to the density-preservation theorem (Theorem 4.1), through Corollaries 3.15 and 3.16. The paper cites it (Lemma 3.3 of Lee 2024) without proof.
--
--   Differences from the source:
--   - encoding: distributions over ([n] k) and base-2 KL divergence → `PMF (Finset (Fin n))` with support in the k-element sets, `klBits` = Mathlib's klDiv of the induced measures divided by ln 2, and an `ENNReal` product on the right-hand side; reason: on the discrete σ-algebra of `Finset (Fin n)` this is the finite sum of Definition 3.9; both sides are finite because U_k has full support on the k-sets
-- source:
--   Aaron Putterman, Sanjeev Khanna, Junkai Song, STOC 2027 submission #589 (October 2026), A Near-Optimal Parallel Algorithm for Finding Matroid Bases, PDF sha256 71ee2ac010ac681077fc3191139efe918fa4a9b8c6dad648fac2ec33016764d6, Lemma 3.14, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_ParallelMatroidBasis_Main_KL

noncomputable section
open Classical MeasureTheory

namespace ParallelMatroidBasis.Main

/-- Lemma 3.14 (KL-contraction), PDF p.14 (printed p.12). For integers `0 < k ≤ n` and every
distribution `μ` over `([n] choose k)`,
`d_KL(D_{k→k−1}(μ) ‖ U_{k−1}) ≤ (1 − 1/k) · d_KL(μ ‖ U_k)`. -/
theorem lemma_3_14 (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n) (μ : PMF (Finset (Fin n)))
    (hμ : IsDistOn n k μ) :
    klBits (downStep n μ).toMeasure (uniformK n (k - 1)).toMeasure ≤
      ENNReal.ofReal (1 - 1 / (k : ℝ)) * klBits μ.toMeasure (uniformK n k).toMeasure := by sorry

end ParallelMatroidBasis.Main
