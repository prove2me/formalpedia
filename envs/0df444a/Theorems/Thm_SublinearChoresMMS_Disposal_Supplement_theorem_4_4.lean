-- Prove2me | Theorems.Thm_SublinearChoresMMS_Disposal_Supplement_theorem_4_4
-- name    : SublinearChoresMMS.Disposal.Supplement.theorem_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:03:26.346131+00:00
-- url     : https://prove2.me/theorems/6f19a174-a361-46e9-b0f4-0512ce0cd673
-- title:
--   Theorem 4.4 — PROP, MMS1 and exact 4/3-MMS
-- statement:
--   Let $n\ge1$ agents have arbitrary nonnegative real additive costs on a finite set $M$ of $m\ge0$ chores. There is one finite probability law $P$ of complete allocations such that
--
--   $$\mathbb E_P[c_i(X_i)]\le\frac{c_i(M)}n\quad(i\in[n]).$$
--
--   Every positive-weight outcome satisfies, for every agent $i$, both
--
--   $$X_i\text{ is MMS1},\qquad c_i(X_i)\le\frac43\mu_i,$$
--
--   where $\mu_i$ is the original full-set $n$-part cost minimax share. All clauses concern the same law. Zero costs, zero MMS, ties, empty chores and empty bundles are included. This companion theorem supplies a uniform worst-case multiplicative bound alongside MMS1 and ex-ante proportionality.
--
--   Differences from the source:
--   - encoding: finite agents, chores, complete partitions and finite lotteries → zero-based Fin labels, owner maps and published finite real-weight laws with positive-weight support; reason: bijections cover exactly the finite source instances, and repeated lottery atoms can be merged
--   - encoding: cost minimax share over all positive-part-count labelled partitions → the published costShare, the negative of the goods maximin functional on negative additive costs; reason: finite sign duality gives the same attained minimax without imposing any goods nonnegativity predicate
-- source:
--   Zehan Lin, Xiaowei Wu, Shengwei Zhou, STOC 2027 submission #845 (October 2026), Theorem 4.4, printed p. 16 / PDF p. 17. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/845.pdf

import Mathlib
import Definitions.Def_SublinearChoresMMS_Disposal_Setting

namespace SublinearChoresMMS.Disposal.Supplement

/-- Theorem 4.4, printed 16 / PDF 17. No ordering, normalization or strict
positivity assumption restricts the original nonnegative real instance. -/
theorem theorem_4_4 (n m : ℕ) (hn : 0 < n) (c : Cost n m) (hc : Nonnegative c) :
    ∃ P : FiniteLaw (Allocation n m),
      (∀ i, P.mean (fun X => cost c i (bundle X i)) ≤ propShare c i) ∧
      ∀ a, 0 < P.weight a → ∀ i,
        MMS1 c i (bundle (P.atom a) i) ∧
        cost c i (bundle (P.atom a) i) ≤ (4 / 3 : ℝ) * mu c i := by sorry

end SublinearChoresMMS.Disposal.Supplement
