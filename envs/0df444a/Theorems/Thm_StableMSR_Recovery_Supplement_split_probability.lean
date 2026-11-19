-- Prove2me | Theorems.Thm_StableMSR_Recovery_Supplement_split_probability
-- name    : StableMSR.Recovery.Supplement.split_probability
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T03:14:09.716959+00:00
-- url     : https://prove2.me/theorems/0727e1c0-e016-49ed-9f34-9142d9782ea4
-- title:
--   Lemma A.2 — splitting probability and expectation
-- statement:
--   Let a finite metric input with $1\le k<n$ be $\gamma$-stable, where $1<\gamma<2$. Set $\varepsilon=\gamma-1$, take the correct guess $\widehat R=R=\max r(C)$, and assume $\sigma R\le L\le\rho$ and $V\ne\varnothing$. Sample a uniform order of $V$ and an independent uniform radius in $[L/16,L/8]$. For every large optimal cluster $C$ of radius $r(C)$, and for $Z$ counting the large clusters split by the final adjusted partition,
--
--   $$\Pr[C\text{ split}]\le\frac{\chi r(C)}L\log(1+12\sigma/\varepsilon^2),\qquad
--   \mathbb EZ\le\frac{\chi M}L\log(1+12\sigma/\varepsilon^2).$$
--
--   Here $\sigma=512$, $\chi=96$, and the logarithm is natural. Both conclusions use the specified partition construction, including the simultaneous component adjustment. This is the quantitative splitting estimate used by the scale-success lemma.
--
--   Differences from the source:
--   - encoding: Finite ordered metric input and unordered exact-k partitions → Fin n points, real metric arrays, and finite sets of nonempty disjoint blocks; reason: Input-order relabelling preserves every source instance and partition; base published definitions are reused without extra conditions
--   - encoding: Uniform order and independent auxiliary radius; expectation of the split count → Finite uniform Dirac mixture times normalized interval volume, and the finite sum of split-event probabilities; reason: This is exactly the product analysis law and the expectation of the finite sum of indicators; it avoids a nonintegrable Bochner default
-- source:
--   Shyam Ravichandran, Lev Reyzin, STOC 2027 submission #1010 (October 2026), Lemma A.2, p. 17; PDF SHA256 8bb34b0b6d31458fe6fc0848c1fc82a6083f3e9ae672e748d24cf82d5289e53e

import Definitions.Def_StableMSR_Recovery_Supplement_Partitions

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery.Supplement

theorem split_probability {n k : ℕ} (d : Point n → Point n → ℝ) (γ L : ℝ) (O : Partition n)
    (hk : 1 ≤ k) (hkn : k < n) (hd : IsMetricArray d) (hγ : 1 < γ ∧ γ < 2)
    (hO : Stable d k γ O)
    (hV : netVertices d (largestRadius d O) L ≠ ∅)
    (hL : sigma * largestRadius d O ≤ L ∧ L ≤ densityScale d O (γ - 1)) :
    (∀ C ∈ largeClusters d O (γ - 1),
      (analysisLaw d (largestRadius d O) L)
        {p | Split C (partitionAt d (γ - 1) (largestRadius d O) L p.2 p.1)} ≤
        ENNReal.ofReal (chi * radius d C / L * Real.log (1 + 12 * sigma / (γ - 1) ^ 2))) ∧
    splitExpectation d O (γ - 1) (largestRadius d O) L ≤
      chi * largeMass d O (γ - 1) / L * Real.log (1 + 12 * sigma / (γ - 1) ^ 2) := by sorry

end StableMSR.Recovery.Supplement
