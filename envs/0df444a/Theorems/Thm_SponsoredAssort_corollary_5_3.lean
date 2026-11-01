-- Prove2me | Theorems.Thm_SponsoredAssort_corollary_5_3
-- name    : SponsoredAssort.corollary_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:53:27.193932+00:00
-- url     : https://prove2.me/theorems/dfa81c39-35b2-45a8-87a9-b6b0d8f5cae4
-- title:
--   Corollary 5.3 — nested partition mechanisms are IC and IR (corrected: nested partitions $P_k$; payment rule)
-- statement:
--   Let the revenues satisfy $r_1\ge\dots\ge r_n>0$, let $k\in[n]$ and let $P_k=\{\{1,\dots,k\},\{k+1\},\dots,\{n\}\}$. For every selector $S^{P_k}(v)\in\arg\max_{T\in P_k}R(T,v)$, the partition mechanism $m^{P_k}$
--
--   1. satisfies (IC),
--   2. satisfies (IR), and
--   3. charges nonnegative payments.
--
--   In particular $m^{\downarrow}=m^{P_1}$ belongs to $M$, which gives the lower bound $\gamma^{PI}(r)\ge1/n$ of §5.3, and the mechanisms of §5.4 are truthful.
--
--   Differences from the source:
--   - correction: for any partition $P$ → for the nested partitions $P_k$, $k\in[n]$; reason: false in general: for $r=(10,10,1)$, $P=\{\{1\},\{2,3\}\}$, $v_1=1$, $v_2=9$, the part $\{2,3\}$ is the unique maximizer for $v_3<10$ and $\{1\}$ for $v_3>10$, so seller 3 is displayed at low and dropped at high attractiveness and no payment makes $m^P$ IC; Appendix G.2 relies on $R(\hat S_i,v)$ increasing in $v_i$, which fails; the $P_k$ are the only partitions the paper uses
--   - correction: payment (3), charging whenever $\hat v_i^P(v_{-i})\le v_i$ → charging only displayed sellers (the sentence after (3)); reason: at a tie (3) charges a seller who is not displayed: $r=(2,1)$, singletons, $v=(1/3,1)$ give $R(\{1\},v)=R(\{2\},v)$ and utility $-1/2$ for the seller left out
--   - generalization: $S^P(v)=\arg\max_\ell R(S_\ell,v)$ with ties unresolved → every welfare-maximizing selector; reason: the statement holds for every tie-breaking rule
--   - generalization: (IC) and (IR) → (IC), (IR) and nonnegative payments; reason: an extra true conclusion; step 3 on p.9 asks for $p_i\ge0$
--   - encoding: $k\in[n]$, sellers $1,\dots,n$ → $1\le k\le n$, sellers `Fin n`; reason: 0-based indexing
-- source:
--   Balseiro, Désir, Incentive-Compatible Assortment Optimization for Sponsored Products, SSRN 3821382 (Feb. 21, 2022), Corollary 5.3, p.27 (proof: Appendix G.2, OA pp.37–38)

import Mathlib
import Definitions.Def_SponsoredAssort_IsIC
import Definitions.Def_SponsoredAssort_IsIR
import Definitions.Def_SponsoredAssort_IsBestSelector
import Definitions.Def_SponsoredAssort_partitionMech
import Definitions.Def_SponsoredAssort_nested

open scoped NNReal

namespace SponsoredAssort

/-- **Corollary 5.3 (Truthfulness of `m^P`)** (Balseiro, Désir, SSRN 3821382 (Feb. 21, 2022),
p.27), corrected to the nested partitions. Let `r₁ ≥ ⋯ ≥ rₙ > 0`, `k ∈ [n]`, and
`P_k = {{1, …, k}, {k+1}, …, {n}}`. For every pointwise welfare-maximizing selector `S^P` over the
parts of `P_k`, the partition mechanism `m^{P_k}` satisfies (IC) and (IR), and its payments are
nonnegative.

**Formalization Note.** The printed "for any partition `P`" is false: for `r = (10, 10, 1)`,
`P = {{1}, {2, 3}}`, `v₁ = 1`, `v₂ = 9`, the part `{2, 3}` is the unique maximizer for `v₃ < 10`
and `{1}` for `v₃ > 10`, so seller 3 is displayed at low and dropped at high attractiveness, and
no payment makes `m^P` (IC). The statement covers the nested partitions `P_k`, the only partitions
the paper uses (`P₁` for `m↓` in §5.3, `P_k` in §5.4). The payment is the rule stated after (3)
(see `partitionMech`). -/
theorem corollary_5_3 {n : ℕ} (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) (hanti : Antitone r) (k : ℕ)
    (hk : 1 ≤ k) (hkn : k ≤ n) (S : Attr n → Finset (Fin n))
    (hS : IsBestSelector r (nested n k) S) :
    IsIC r (partitionMech r (nested n k) S) ∧ IsIR r (partitionMech r (nested n k) S) ∧
      ∀ v i, 0 ≤ (partitionMech r (nested n k) S).pay v i := by sorry

end SponsoredAssort
