-- Prove2me | Theorems.Thm_SingleOrSample_Supplement_theorem_3_6
-- name    : SingleOrSample.Supplement.theorem_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:36:12.472346+00:00
-- url     : https://prove2.me/theorems/acea3e7e-8824-46bf-9068-fb6baea00429
-- title:
--   Theorem 3.6 — Algorithm 1 with the adaptive safe strategies of Definition 6 gives every submodular agent $1/12$-MMS with probability $\ge1-ne^{-n/10}$
-- statement:
--   Let $n$ agents have monotone, normalized ($v_i(\emptyset)=0$), submodular valuations $v_1,\dots,v_n$ on $m$ goods, and suppose
--   $$
--   v_i(\{e\})<\tfrac1{12}\,\mathrm{MMS}_i\qquad\text{for all agents } i \text{ and goods } e.
--   $$
--   If every agent follows the safe strategy of Definition 6 to form her buckets adaptively within Algorithm 1 (each bucket is the $3n$ goods not yet bucketed with the highest marginal values relative to the goods picked so far in the round, ties broken arbitrarily), then
--   $$
--   \Pr\Bigl[\text{the bundles are pairwise disjoint and } v_i(A_i)\ge\tfrac1{12}\mathrm{MMS}_i\ \text{for all } i\Bigr]\ \ge\ 1-n\,e^{-n/10}.
--   $$
--
--   This extends Theorem 3.3 from additive to submodular agents in the absence of large items, and is the template for the main algorithm of Section 4.
--
--   **Formalization Note** As in Theorem 3.3, the paper's normalization $\mathrm{MMS}_i=1$ is replaced by scaling the assumption and the conclusion; marginal values scale with $v_i$, so Definition 6 is unchanged.
--
--   Differences from the source:
--   - encoding: normalized instance (MMS_i = 1, Definition 3) with v_i(e) < 1/12 and target 1/12 → unnormalized valuations with v_i({e}) < MMS_i/12 and conclusion MMS_i/12 ≤ v_i(A_i); reason: Appendix A: scaling v_i by 1/MMS_i changes neither Algorithm 1 nor the bucket choices of Definitions 5–6; when m > 0 the hypothesis forces MMS_i > 0
--   - encoding: Definition 6 with ties broken arbitrarily → IsSafeDef6: every bucket is 3n goods of G with the largest marginal values given the picks so far, every tie-breaking allowed; reason: the page leaves ties open
--   - encoding: agent i specifies a partition R_i = B_i1 ∪ … ∪ B_iℓi with ℓ_i = ⌈|R_i|/3n⌉ and samples the first ℓ_i − 1 buckets by SwR(B_ij, 1/(3n)) → alg1Law: buckets of size 3n are formed and one uniform item of each is allocated while more than 3n goods are not yet in a bucket; reason: this samples exactly ℓ_i − 1 buckets; SwR(B, 1/(3n)) on |B| = 3n returns exactly one uniform item
--   - encoding: allocates to every agent simultaneously a 1/12-MMS → the bundles are pairwise disjoint (LittleCharity.EFX.IsPartialAllocation) and every agent gets at least MMS_i/12; reason: Algorithm 1 may leave goods unallocated; valuations are monotone, so leftovers can go to anyone
--   - encoding: submodular valuation (with the standing v_i non-negative, non-decreasing, v_i(∅) = 0 of §2.1) → SingleOrSample.IsValuation ∧ SubsamplingSM.Offline.IsSubmodular; reason: the published base definitions, as in the base goal
--   - encoding: agents 1, …, n → Fin n, from 0; reason: Lean convention; same instances
-- source:
--   Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), Theorem 3.6, p.12 (pdf p.14); standing assumptions of §3, pp.9–10; Definition 6, p.10

import Mathlib
import Definitions.Def_LittleCharity_EFX_Setting
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular
import Definitions.Def_SingleOrSample_IsValuation
import Definitions.Def_SingleOrSample_Hist
import Definitions.Def_SingleOrSample_Strategy
import Definitions.Def_SingleOrSample_Supplement_alg1Law
import Definitions.Def_SingleOrSample_Supplement_IsSafeAlg1

namespace SingleOrSample.Supplement

open SingleOrSample

/-- **Theorem 3.6** (Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial
Agents, STOC 2027 submission, arXiv:2609.32286, manuscript sha256 28cd3d7b…, Theorem 3.6, p.12, under the standing assumptions of §3, pp.9–10). Let `n`
agents have monotone, normalized, submodular valuations with every single item worth less than
`MMS_i/12`. If every agent follows the safe strategy of Definition 6 (adaptive greedy buckets by
marginal value) in Algorithm 1, then with probability at least `1 − n e^{−n/10}` the bundles are
pairwise disjoint and every agent gets at least `MMS_i/12`.

**Formalization Note.** Scaled by `MMS_i` as in Theorem 3.3 (Appendix A; marginal values scale with
`v`). `MMS_i` partitions all `m` goods into `n` bundles. -/
theorem theorem_3_6 (n m : ℕ) (vs : Fin n → Finset (Fin m) → ℝ)
    (hv : ∀ i, IsValuation (vs i) ∧ SubsamplingSM.Offline.IsSubmodular (vs i))
    (hsmall : ∀ (i : Fin n) (e : Fin m),
      vs i {e} < (1 / 12) * LittleCharity.MMS.mms (vs i) n Finset.univ)
    (σ : Fin n → Strategy m) (hσ : ∀ i, IsSafeDef6 n (vs i) (σ i)) :
    ENNReal.ofReal (1 - (n : ℝ) * Real.exp (-(n : ℝ) / 10)) ≤ (alg1Law σ n).toOuterMeasure
      {h | LittleCharity.EFX.IsPartialAllocation (fun i : Fin n => (allocOf h i : Finset (Fin m))) ∧
        ∀ i, (1 / 12) * LittleCharity.MMS.mms (vs i) n Finset.univ ≤ vs i (allocOf h i)} := by sorry

end SingleOrSample.Supplement
