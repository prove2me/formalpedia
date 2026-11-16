-- Prove2me | Theorems.Thm_SublinearChoresMMS_Disposal_Supplement_lemma_4_2
-- name    : SublinearChoresMMS.Disposal.Supplement.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:01:54.433354+00:00
-- url     : https://prove2.me/theorems/349e4c16-32eb-4e24-8150-cf556ea91b5e
-- title:
--   Lemma 4.2 — Algorithm 1 fractional completion
-- statement:
--   In the normalized Section 4 setting with $n\ge1$ and $m\ge2n$, Algorithm 1 produces a finite probability law $F$ of complete fractional allocations. Each output retains the assigned opposite-pair permutation and tail fractions $t_i\in[0,1]$ summing to one. Write $x_i=\mathbf1_{Q^i}+t_i\mathbf1_V$. Then
--
--   $$\mathbb E_F[c_i(x_i)]\le\frac{c_i(M)}n\quad\text{for every }i.$$
--
--   In every positive-weight output,
--
--   $$t_i>0\implies c_i(x_i)\le\frac{c_i(M)}n.$$
--
--   The law is exactly the operational Algorithm 1 weighted list, whose probability normalization and completeness are also asserted. This is the fractional completion result used in the tail rounding step.
--
--   Differences from the source:
--   - encoding: the constructed opposite pairs and a possibly empty tail in the normalized IDO regime → oppositePairs and oppositeTail with 2*n≤m and the published Normalized predicate; reason: zero-based pairing j with 2*n-1-j is the same construction; the normalization, positivity and strict order are internal section assumptions
--   - encoding: Algorithm 1 with an arbitrary maximizing-agent choice, cheapest-bundle choices and two uniform random choices → the explicit recursive weighted list algorithm1 with index tie breaking, plus concluded probability normalization and completeness; reason: every chosen action obeys the algorithm, the full-completion permutations enumerate the residual bijections exactly once, and no cost bound is an input certificate
--   - encoding: finite agents, chores, complete partitions and finite lotteries → zero-based Fin labels, owner maps and published finite real-weight laws with positive-weight support; reason: bijections cover exactly the finite source instances, and repeated lottery atoms can be merged
--   - encoding: cost minimax share over all positive-part-count labelled partitions → the published costShare, the negative of the goods maximin functional on negative additive costs; reason: finite sign duality gives the same attained minimax without imposing any goods nonnegativity predicate
-- source:
--   Zehan Lin, Xiaowei Wu, Shengwei Zhou, STOC 2027 submission #845 (October 2026), Lemma 4.2, printed p. 15 / PDF p. 16. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/845.pdf

import Mathlib
import Definitions.Def_SublinearChoresMMS_Disposal_Supplement_FixedBundles

namespace SublinearChoresMMS.Disposal.Supplement

/-- Lemma 4.2, printed 15 / PDF 16: the law is Algorithm 1, not an arbitrary
fairness-certified input. Assigned pairs and the common-tail fractions are retained. -/
theorem lemma_4_2 (n m : ℕ) (hn : 0 < n) (hm : 2 * n ≤ m)
    (c : Cost n m) (hc : Normalized c) :
    ∃ F : FiniteLaw (Completion n),
      F.toLaw = algorithm1 c (oppositePairs n m) (oppositeTail n m) ∧
      (∀ i, F.mean (fun z => fractionalCost c i
        (completionFraction (oppositePairs n m) (oppositeTail n m) z i)) ≤ propShare c i) ∧
      ∀ a, 0 < F.weight a →
        Complete (F.atom a) ∧
        ∀ i, 0 < (F.atom a).tail i →
          fractionalCost c i (completionFraction (oppositePairs n m) (oppositeTail n m)
            (F.atom a) i) ≤ propShare c i := by sorry

end SublinearChoresMMS.Disposal.Supplement
