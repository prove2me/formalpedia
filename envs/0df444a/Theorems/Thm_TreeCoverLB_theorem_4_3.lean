-- Prove2me | Theorems.Thm_TreeCoverLB_theorem_4_3
-- name    : TreeCoverLB.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:25:51.815194+00:00
-- url     : https://prove2.me/theorems/3c74662c-c515-413f-99a5-5b08dfb0059f
-- title:
--   Theorem 4.3: distortion lower bound $c\,n^{1/(d+1)}$ from the agreement index
-- statement:
--   Let $p$ be prime and $k\ge 2$, and let $d$ be such that there is a continuous $\mathbb Z_p$-equivariant map $|I_{p,k}|\to|E_d\mathbb Z_p|$, i.e. $\operatorname{ind}_{\mathbb Z_p}(|I_{p,k}|)\le d$. There are $c>0$ and $N_0$ such that for every integer $n\ge N_0$ there is an $n$-point metric for which every size-$k$ tree cover has distortion at least
--   $$
--   c\,n^{1/(d+1)} .
--   $$
--
--   Every upper bound on the agreement index thus gives a polynomial lower bound for tree covers.
--
--   Differences from the source:
--   - generalization: d := ind_{ℤ_p}(|I_{p,k}|) → every d admitting a continuous ℤ_p-equivariant map |I_{p,k}| → |E_dℤ_p|; reason: the index is finite (Lemma 5.5) and is the least such d; at d = ind the statement is the paper's
--   - encoding: an n-point metric X_n; c = c(p, k, d) and 'sufficiently large n' → a metric function on Fin n; ∃ c > 0, ∃ N₀ before n; reason: the meaning of the notation; trees live on exactly the n points
-- source:
--   Chen, Huang, Tan, Xu, Improved Lower Bounds on Tree Covers, arXiv:2607.27264 (version of October 31, 2026), Theorem 4.3, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_TreeCoverLB_IsFinMetric
import Definitions.Def_TreeCoverLB_WeightedTree
import Definitions.Def_TreeCoverLB_IsTreeCover
import Definitions.Def_TreeCoverLB_realization
import Definitions.Def_TreeCoverLB_EJoin
import Definitions.Def_TreeCoverLB_agreementComplex
import Definitions.Def_TreeCoverLB_IsAgreementIndexMap

open Classical

namespace TreeCoverLB

/-- **Theorem 4.3 (Distortion lower bound from the agreement index)** (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), Theorem 4.3, p.11
(PDF p.13)): let `p` be a prime and `k ≥ 2`, and let `d` be such that there is a continuous
`ℤ_p`-equivariant map `|I_{p,k}| → |E_dℤ_p|` (i.e. `ind_{ℤ_p}(|I_{p,k}|) ≤ d`). There is a constant
`c = c(p, k, d) > 0` such that, for every sufficiently large integer `n`, there is an `n`-point metric
for which every `k`-tree cover has distortion at least `c n^{1/(d+1)}`.

**Formalization Note** The paper puts `d := ind_{ℤ_p}(|I_{p,k}|)`. This index is finite (`|I_{p,k}|` is a
finite complex with a free simplicial action, so Lemma 5.5 applies) and is the least `d` admitting
such a map; the statement is posed for every such `d`, and at `d = ind` it is the paper's. `c` and
`N₀` are chosen before `n`; the metric is a function on `Fin n` (`IsFinMetric`), and the trees live on
exactly these `n` points. -/
theorem theorem_4_3 (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 2 ≤ k) (d : ℕ)
    (hψ : ∃ ψ : ((Fin k → ZMod p) → ℝ) → (Fin (d + 1) × ZMod p → ℝ),
      IsAgreementIndexMap p k d ψ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ dist : Fin n → Fin n → ℝ, IsFinMetric dist ∧
        ∀ (T : Fin k → WeightedTree (Fin n)) (α : ℝ), IsTreeCover dist T α →
          c * (n : ℝ) ^ ((1 : ℝ) / ((d : ℝ) + 1)) ≤ α := by sorry

end TreeCoverLB
