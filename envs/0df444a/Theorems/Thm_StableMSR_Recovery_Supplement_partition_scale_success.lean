-- Prove2me | Theorems.Thm_StableMSR_Recovery_Supplement_partition_scale_success
-- name    : StableMSR.Recovery.Supplement.partition_scale_success
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:14:34.68299+00:00
-- url     : https://prove2.me/theorems/7d7f41d7-91e1-43a0-9dcb-e26873a6cd71
-- title:
--   Lemma A.4 — dyadic scale and successful partition
-- statement:
--   Let $1\le k<n$, let $1<\gamma<2$, and let $\mathcal O$ be the $\gamma$-stable optimum of the finite metric input. Write $\varepsilon=\gamma-1$, $R=\max r(C)$, $M=\sum_{C\in\mathcal T}r(C)$, $t=|\mathcal T|$, and $\rho=\varepsilon M/4$. If $\rho<\sigma R$, then $t\le N_\varepsilon$. Otherwise there is an integer $9\le j\le\lceil\log_2 n\rceil$ such that $L=2^jR$ obeys
--
--   $$\sigma R\le L\le\rho<2L,\qquad M/L<8/\varepsilon,$$
--
--   and RandomPartitions$(R,L)$ contains a partition splitting at most $F_\varepsilon$ large clusters with probability at least $1/3$. This probability is over its single uniform order; every prescribed midpoint radius is enumerated. The constants are $\sigma=512$, $N_\varepsilon=\lceil16\sigma/\varepsilon^2\rceil$, and $F_\varepsilon=\lceil12\chi\Lambda_\varepsilon/\varepsilon\rceil$, with $\chi=96$ and $\Lambda_\varepsilon=\lceil\log_2(1+12\sigma/\varepsilon^2)\rceil$.
--
--   The statement includes both scale selection and the full probability guarantee.
--
--   Differences from the source:
--   - encoding: Finite ordered metric input and unordered exact-k partitions → Fin n points, real metric arrays, and finite sets of nonempty disjoint blocks; reason: Input-order relabelling preserves every source instance and partition; base published definitions are reused without extra conditions
--   - encoding: log_2 sigma <= j <= ceil(log_2 n) → Natural j with 9 <= j <= the natural ceiling of logb 2 n; reason: sigma = 512 = 2^9 and n >= 2 under the section hypotheses, so the index sets agree
-- source:
--   Shyam Ravichandran, Lev Reyzin, STOC 2027 submission #1010 (October 2026), Lemma A.4, p. 20; PDF SHA256 8bb34b0b6d31458fe6fc0848c1fc82a6083f3e9ae672e748d24cf82d5289e53e

import Definitions.Def_StableMSR_Recovery_Supplement_Partitions

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery.Supplement

theorem partition_scale_success {n k : ℕ} (d : Point n → Point n → ℝ) (γ : ℝ) (O : Partition n)
    (hk : 1 ≤ k) (hkn : k < n) (hd : IsMetricArray d) (hγ : 1 < γ ∧ γ < 2)
    (hO : Stable d k γ O) :
    (densityScale d O (γ - 1) < sigma * largestRadius d O →
      (largeClusters d O (γ - 1)).card ≤ fewBound (γ - 1)) ∧
    (sigma * largestRadius d O ≤ densityScale d O (γ - 1) →
      ∃ j : ℕ, 9 ≤ j ∧ j ≤ ⌈Real.logb 2 n⌉₊ ∧
        let L := (2 : ℝ) ^ j * largestRadius d O
        sigma * largestRadius d O ≤ L ∧ L ≤ densityScale d O (γ - 1) ∧
        densityScale d O (γ - 1) < 2 * L ∧ largeMass d O (γ - 1) / L < 8 / (γ - 1) ∧
        (orderLaw (netVertices d (largestRadius d O) L))
          {π | ∃ Q ∈ randomPartitions d (γ - 1) (largestRadius d O) L π,
            splitCount d O (γ - 1) Q ≤ splitBound (γ - 1)} ≥ (1 / 3 : ENNReal)) := by sorry

end StableMSR.Recovery.Supplement
