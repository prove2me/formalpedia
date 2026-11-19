-- Prove2me | Theorems.Thm_StableMSR_Recovery_Supplement_net_counts
-- name    : StableMSR.Recovery.Supplement.net_counts
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T03:13:33.763466+00:00
-- url     : https://prove2.me/theorems/c4f8e4cf-9857-46be-b291-f672cda2123b
-- title:
--   Lemma A.1 — inner and outer net counts
-- statement:
--   Let $\mathcal O$ be a $\gamma$-stable optimum, $1\le k<n$, $1<\gamma<2$, $\varepsilon=\gamma-1$, and $R=\max r(C)$. Suppose $\sigma R\le L\le\rho$, where $\sigma=512$ and $\rho=\varepsilon M/4$. For every wide $G_R$-component $U$ and $x\in U$, the input-order greedy net satisfies
--
--   $$|N_U\cap B(x,L/32)|\ge\frac L{\sigma R},\qquad
--   |N_U\cap B(x,L/4)|\le\frac{12L}{\varepsilon^2R}.$$
--
--   Both bounds concern the same prescribed net. They control the number of inner centers and potentially relevant outer centers in the splitting estimate.
--
--   Differences from the source:
--   - encoding: Finite ordered metric input and unordered exact-k partitions → Fin n points, real metric arrays, and finite sets of nonempty disjoint blocks; reason: Input-order relabelling preserves every source instance and partition; base published definitions are reused without extra conditions
-- source:
--   Shyam Ravichandran, Lev Reyzin, STOC 2027 submission #1010 (October 2026), Lemma A.1, p. 16; PDF SHA256 8bb34b0b6d31458fe6fc0848c1fc82a6083f3e9ae672e748d24cf82d5289e53e

import Definitions.Def_StableMSR_Recovery_Supplement_Partitions

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery.Supplement

theorem net_counts {n k : ℕ} (d : Point n → Point n → ℝ) (γ L : ℝ) (O : Partition n)
    (hk : 1 ≤ k) (hkn : k < n) (hd : IsMetricArray d) (hγ : 1 < γ ∧ γ < 2)
    (hO : Stable d k γ O)
    (hL : sigma * largestRadius d O ≤ L ∧ L ≤ densityScale d O (γ - 1))
    (U : Cluster n) (hU : U ∈ wideComponents d (largestRadius d O) L)
    (x : Point n) (hx : x ∈ U) :
    L / (sigma * largestRadius d O) ≤
      ((greedyNet d (largestRadius d O) U ∩ ball d x (L / 32)).card : ℝ) ∧
    ((greedyNet d (largestRadius d O) U ∩ ball d x (L / 4)).card : ℝ) ≤
      12 * L / ((γ - 1) ^ 2 * largestRadius d O) := by sorry

end StableMSR.Recovery.Supplement
