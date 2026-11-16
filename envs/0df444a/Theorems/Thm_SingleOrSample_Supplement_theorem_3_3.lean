-- Prove2me | Theorems.Thm_SingleOrSample_Supplement_theorem_3_3
-- name    : SingleOrSample.Supplement.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:35:37.323487+00:00
-- url     : https://prove2.me/theorems/dd1934cd-ad85-4249-a02b-3f70165896b8
-- title:
--   Theorem 3.3 — Algorithm 1 with the safe strategies of Definition 5 gives every additive agent $1/12$-MMS with probability $\ge1-ne^{-n/10}$
-- statement:
--   Let $n$ agents have additive valuations $v_1,\dots,v_n$ on $m$ goods with nonnegative item values, and suppose no single good is worth much to anyone:
--   $$
--   v_i(\{e\})<\tfrac1{12}\,\mathrm{MMS}_i\qquad\text{for all agents } i \text{ and goods } e,
--   $$
--   where $\mathrm{MMS}_i$ is the maximin share of $v_i$ for $n$ bundles of all $m$ goods. If every agent follows the safe strategy of Definition 5 in Algorithm 1 (buckets of $3n$ goods of the largest remaining values, one uniformly random good allocated from each but the last), then
--   $$
--   \Pr\Bigl[\text{the bundles are pairwise disjoint and } v_i(A_i)\ge\tfrac1{12}\mathrm{MMS}_i\ \text{for all } i\Bigr]\ \ge\ 1-n\,e^{-n/10}.
--   $$
--
--   This is the warm-up of the paper: in the absence of large items, static bucketing gives every agent a constant fraction of her maximin share with high probability, whatever the arrival order.
--
--   **Formalization Note** The paper normalizes $\mathrm{MMS}_i=1$; here the assumption and the conclusion are scaled by $\mathrm{MMS}_i$, which leaves Algorithm 1 and Definition 5 unchanged.
--
--   Differences from the source:
--   - encoding: normalized instance (MMS_i = 1, Definition 3) with v_i(e) < 1/12 and target 1/12 → unnormalized valuations with v_i({e}) < MMS_i/12 and conclusion MMS_i/12 ≤ v_i(A_i); reason: Appendix A: scaling v_i by 1/MMS_i changes neither Algorithm 1 nor the bucket choices of Definitions 5–6; when m > 0 the hypothesis forces MMS_i > 0
--   - generalization: Definition 5: a static weakly decreasing order of R_i, cut into buckets of 3n consecutive goods (ties broken arbitrarily, once) → IsSafeDef5: every bucket is 3n goods of G of the largest singleton values, with ties that may be broken depending on the history and the picks so far; reason: every static weakly decreasing order satisfies the predicate, so the theorem specializes to the page's strategies
--   - encoding: agent i specifies a partition R_i = B_i1 ∪ … ∪ B_iℓi with ℓ_i = ⌈|R_i|/3n⌉ and samples the first ℓ_i − 1 buckets by SwR(B_ij, 1/(3n)) → alg1Law: buckets of size 3n are formed and one uniform item of each is allocated while more than 3n goods are not yet in a bucket; reason: this samples exactly ℓ_i − 1 buckets; SwR(B, 1/(3n)) on |B| = 3n returns exactly one uniform item
--   - encoding: allocates to every agent simultaneously a 1/12-MMS → the bundles are pairwise disjoint (LittleCharity.EFX.IsPartialAllocation) and every agent gets at least MMS_i/12; reason: Algorithm 1 may leave goods unallocated; valuations are monotone, so leftovers can go to anyone
--   - encoding: additive valuations → LittleCharity.MMS.IsAdditive: v_i(S) = Σ_{g∈S} v_i({g}) and v_i ≥ 0; reason: §2.1, p.6; nonnegativity is the standing v_i : 2^[m] → ℝ₊
--   - encoding: agents 1, …, n → Fin n, from 0; reason: Lean convention; same instances
-- source:
--   Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), Theorem 3.3, p.10 (pdf p.12); standing assumptions of §3, p.9 (Algorithm 1, Require line); Definition 5, p.9

import Mathlib
import Definitions.Def_LittleCharity_EFX_Setting
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_SingleOrSample_Hist
import Definitions.Def_SingleOrSample_Strategy
import Definitions.Def_SingleOrSample_Supplement_alg1Law
import Definitions.Def_SingleOrSample_Supplement_IsSafeAlg1

namespace SingleOrSample.Supplement

open SingleOrSample

/-- **Theorem 3.3** (Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial
Agents, STOC 2027 submission, arXiv:2609.32286, manuscript sha256 28cd3d7b…, Theorem 3.3, p.10, under the standing assumptions of §3, p.9). Let `n`
agents have additive valuations with every single item worth less than `MMS_i/12`. If every agent
follows the safe strategy of Definition 5 in Algorithm 1, then with probability at least
`1 − n e^{−n/10}` the bundles are pairwise disjoint and every agent gets at least `MMS_i/12`.

**Formalization Note.** §3 normalizes `MMS_i = 1` and assumes `v_i(e) < 1/12`; here the valuations
are unnormalized and the assumption and the conclusion are scaled by `MMS_i` (Appendix A; Algorithm 1
and Definition 5 are invariant under scaling). `MMS_i` partitions all `m` goods into `n` bundles.
Additivity with nonnegative item values is the published `LittleCharity.MMS.IsAdditive`. -/
theorem theorem_3_3 (n m : ℕ) (vs : Fin n → Finset (Fin m) → ℝ)
    (hadd : LittleCharity.MMS.IsAdditive vs)
    (hsmall : ∀ (i : Fin n) (e : Fin m),
      vs i {e} < (1 / 12) * LittleCharity.MMS.mms (vs i) n Finset.univ)
    (σ : Fin n → Strategy m) (hσ : ∀ i, IsSafeDef5 n (vs i) (σ i)) :
    ENNReal.ofReal (1 - (n : ℝ) * Real.exp (-(n : ℝ) / 10)) ≤ (alg1Law σ n).toOuterMeasure
      {h | LittleCharity.EFX.IsPartialAllocation (fun i : Fin n => (allocOf h i : Finset (Fin m))) ∧
        ∀ i, (1 / 12) * LittleCharity.MMS.mms (vs i) n Finset.univ ≤ vs i (allocOf h i)} := by sorry

end SingleOrSample.Supplement
