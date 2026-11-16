-- Prove2me | Theorems.Thm_SublinearChoresMMS_Disposal_Supplement_lemma_4_1
-- name    : SublinearChoresMMS.Disposal.Supplement.lemma_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T21:01:22.341983+00:00
-- url     : https://prove2.me/theorems/a68d3304-2c44-46de-a8c0-a81ee0fa2a20
-- title:
--   Lemma 4.1 — opposite-pair and tail bounds
-- statement:
--   In the Section 4 regime, let $n\ge1$, $m\ge2n$, and let the costs be positive, strictly decreasing in the common chore order, with $\mu_i=1$. For the constructed opposite pairs and tail, every agent satisfies
--
--   $$c_i(g)\le\frac13\quad(g\in V),\qquad c_i(Q_j)\le\frac43\quad(j\in[n]).$$
--
--   The tail bound is pointwise and therefore includes $V=\varnothing$. Both conclusions control the same constructed decomposition used by Theorem 4.4.
--
--   Differences from the source:
--   - encoding: the constructed opposite pairs and a possibly empty tail in the normalized IDO regime → oppositePairs and oppositeTail with 2*n≤m and the published Normalized predicate; reason: zero-based pairing j with 2*n-1-j is the same construction; the normalization, positivity and strict order are internal section assumptions
--   - encoding: finite agents, chores, complete partitions and finite lotteries → zero-based Fin labels, owner maps and published finite real-weight laws with positive-weight support; reason: bijections cover exactly the finite source instances, and repeated lottery atoms can be merged
--   - encoding: cost minimax share over all positive-part-count labelled partitions → the published costShare, the negative of the goods maximin functional on negative additive costs; reason: finite sign duality gives the same attained minimax without imposing any goods nonnegativity predicate
-- source:
--   Zehan Lin, Xiaowei Wu, Shengwei Zhou, STOC 2027 submission #845 (October 2026), Lemma 4.1, printed p. 14 / PDF p. 15. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/845.pdf

import Mathlib
import Definitions.Def_SublinearChoresMMS_Disposal_Supplement_FixedBundles

namespace SublinearChoresMMS.Disposal.Supplement

/-- Lemma 4.1, printed 14 / PDF 15; the section's normalized ordered regime. -/
theorem lemma_4_1 (n m : ℕ) (hn : 0 < n) (hm : 2 * n ≤ m)
    (c : Cost n m) (hc : Normalized c) :
    (∀ i e, e ∈ oppositeTail n m → c i e ≤ (1 / 3 : ℝ)) ∧
    ∀ i j, cost c i (oppositePairs n m j) ≤ (4 / 3 : ℝ) := by sorry

end SublinearChoresMMS.Disposal.Supplement
