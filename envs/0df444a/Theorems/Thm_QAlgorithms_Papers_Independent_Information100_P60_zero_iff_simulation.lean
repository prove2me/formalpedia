-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P60_zero_iff_simulation
-- name    : QAlgorithms.Papers.Independent.Information100.P60.zero_iff_simulation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:36:39.260743+00:00
-- url     : https://prove2.me/theorems/f5065c16-6ca3-49b6-b3f0-948240dd1b00
-- title:
--   Lemma 2: four zero-exponent iff simultaneous-simulation criteria
-- statement:
--   Let $A=\mathbb C^a$ and $B=\mathbb C^b$, with $a,b>0$, let $\mathcal R$ be a nonempty closed convex set of CPTP maps from $A$ to $B$, and let $\mathcal N\notin\mathcal R$ be CPTP. All relative entropies are in bits, ordered as null output versus alternative output. Every channel use applies the same unknown channel independently. Tests accept the null and constrain Type-I error uniformly over $\mathcal R$. Write $E_{r,k}^c$ for the operational BIID exponent with local reference dimension $r$, block size $k\ge1$, and correlation class $c$ (unrestricted, separable across uses, or product). The entire block repeats independently, with a joint final measurement. Here $r=1$ denotes no memory and $r=a$ suffices for memory assistance. Write $E_{r,\mathrm{arb}}^c$ for the independently defined arbitrary parallel-probe exponent. Exponents take values in $[0,\infty]$, and both outer limits of the inner liminf and limsup are understood as the Type-I tolerance decreases to zero. For $r\in\{1,a\}$, $$E_{r,k}^{\mathrm{unrestricted}}=0\iff\forall\sigma\in\mathcal D(\mathbb C^{r^k}\otimes A^{\otimes k}),\ \exists\Phi\in\mathcal R:\ (\operatorname{id}\otimes\Phi^{\otimes k})(\sigma)=(\operatorname{id}\otimes\mathcal N^{\otimes k})(\sigma).$$ Likewise, $$E_{r,k}^{\mathrm{product}}=0\iff\forall(\tau_i)_{i=1}^k,\ \exists\Phi\in\mathcal R,\ \forall i:\ (\operatorname{id}_r\otimes\Phi)(\tau_i)=(\operatorname{id}_r\otimes\mathcal N)(\tau_i),$$ where every $\tau_i$ is a density operator on $\mathbb C^r\otimes A$. These are four equivalences. The simulator depends on the whole probe collection, and must be common to its factors.
-- source:
--   Quantum hypothesis testing of non-mixed-unitarity: A multifaceted hierarchy of quantum channel discrimination, arXiv:2609.40355v1, PDF p. 14, Lemma 2: four zero-exponent iff simultaneous-simulation criteria

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Information100.P60

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv-2609.40355v1, PDF pp.14–15, Lemma 2, all four equivalences (41)–(44). -/
theorem zero_iff_simulation {a b : ℕ} (R : Set (Maps a b)) (N : Maps a b)
    (h : Setting R N) (k : ℕ) (hk : 0 < k) : ∀ r ∈ ({1, a} : Set ℕ),
      (blockExponent r R N k .unrestricted = 0 ↔
        ∀ X, IsDensityMatrix X → ∃ Phi ∈ R, output r k Phi X = output r k N X) ∧
      (blockExponent r R N k .product = 0 ↔
        ∀ tau : Fin k → Mat (Fin r × Fin a), (∀ i, IsDensityMatrix (tau i)) →
          ∃ Phi ∈ R, ∀ i, idTensorSuperop Phi (tau i) = idTensorSuperop N (tau i)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P60

end
