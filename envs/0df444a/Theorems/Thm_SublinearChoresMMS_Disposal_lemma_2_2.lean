-- Prove2me | Theorems.Thm_SublinearChoresMMS_Disposal_lemma_2_2
-- name    : SublinearChoresMMS.Disposal.lemma_2_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-09T03:31:16.557117+00:00
-- url     : https://prove2.me/theorems/9dc9be39-d725-45a9-9ff4-42acce9c5784
-- title:
--   Lemma 2.2 — IDO reduction with itemwise cost domination
-- statement:
--   For every instance with $n\ge1$, finitely many chores, and nonnegative real additive costs, there is a common-rank instance $d$ whose row $d_i$ is a nonincreasing permutation of the original row $c_i$. Each agent's total cost and MMS are unchanged. For every complete rank allocation $A$, there is a bijection $\sigma$ from ranks to actual chores such that
--
--   $$c_{A(r)}(\sigma(r))\le d_{A(r)}(r)\quad\text{for every rank }r.$$
--
--   Give actual chore $\sigma(r)$ to the owner of rank $r$. This is a complete allocation, and every agent's total cost is at most her cost in the rank allocation. The itemwise conclusion retains the information needed to transfer MMS1, including ties, zero costs, empty chore sets, and empty bundles.
--
--   Differences from the source:
--   - encoding: each row is replaced by its sorted cost multiset → existential row permutations with unchanged total cost and MMS, and an existential transfer permutation for every allocation; reason: permutations express the same sorted multiset and distinct actual chores; the benchmark invariances follow from the identical partition problems
--   - encoding: finite agents, chores, complete partitions and finite lotteries → agents Fin n, chores Fin m, allocation maps and normalized finite lists with real weights; reason: bijections identify the same finite instances and partitions; repeated lottery atoms may be merged and positive weights define support
--   - encoding: cost minimax share over labelled partitions → the negative of LittleCharity.MMS.mms evaluated at negative additive bundle costs; reason: negation exchanges finite maxima and minima; no goods nonnegativity predicate is imposed, and costShare_spec states the attained minimax characterization
-- source:
--   Zehan Lin, Xiaowei Wu, Shengwei Zhou, STOC 2027 submission #845 (October 2026), Lemma 2.2, printed p. 5 / PDF p. 6; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/845.pdf

import Mathlib
import Definitions.Def_SublinearChoresMMS_Disposal_Setting

noncomputable section

namespace SublinearChoresMMS.Disposal

/-- Lemma 2.2, printed p. 5 / PDF p. 6: construct sorted rows and an itemwise
cost-dominating transfer for every rank allocation. Ties and zero costs are allowed. -/
theorem lemma_2_2 {n m : ℕ} (hn : 0 < n) (c : Cost n m) (hc : Nonnegative c) :
    ∃ (d : Cost n m) (rowPerm : Fin n → Equiv.Perm (Fin m)),
      IDO d ∧ (∀ i r, d i r = c i (rowPerm i r)) ∧
      (∀ i, mu d i = mu c i ∧ cost d i Finset.univ = cost c i Finset.univ) ∧
      ∀ A : Allocation n m, ∃ transfer : Equiv.Perm (Fin m),
        (∀ r, c (A r) (transfer r) ≤ d (A r) r) ∧
        ∀ i, cost c i (bundle (fun e => A (transfer.symm e)) i) ≤ cost d i (bundle A i) := by sorry

end SublinearChoresMMS.Disposal
