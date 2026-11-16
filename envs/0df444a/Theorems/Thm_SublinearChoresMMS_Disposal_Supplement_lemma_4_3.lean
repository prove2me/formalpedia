-- Prove2me | Theorems.Thm_SublinearChoresMMS_Disposal_Supplement_lemma_4_3
-- name    : SublinearChoresMMS.Disposal.Supplement.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:02:42.22981+00:00
-- url     : https://prove2.me/theorems/5ac759fc-24a1-46bb-a5f4-24eed50ec5e7
-- title:
--   Lemma 4.3 — fixed pairs and rounded tails
-- statement:
--   In the normalized Section 4 setting with $n\ge1$ and $m\ge2n$, the actual Algorithm 1 law can be rounded to one finite law of integral complete allocations while keeping each agent's assigned opposite pair fixed. The law is ex-ante proportional:
--
--   $$\mathbb E[c_i(X_i)]\le\frac{c_i(M)}n.$$
--
--   Every positive-weight outcome simultaneously satisfies MMS1 for every agent and, for each agent $i$,
--
--   $$X_i=Q^i\quad\text{or}\quad\exists e\in X_i\cap V:\ c_i(X_i\setminus\{e\})\le\frac{c_i(M)}n.$$
--
--   The joint law retains the Algorithm 1 support index, its exact marginal, and every conditional tail-slot marginal. Tail matchings use positive-mass edges, fill full tail slots, and leave fixed bundles intact. The removable chore must be in the tail. This preserves the precise disjunction needed by Theorem 4.4.
--
--   Differences from the source:
--   - encoding: the constructed opposite pairs and a possibly empty tail in the normalized IDO regime → oppositePairs and oppositeTail with 2*n≤m and the published Normalized predicate; reason: zero-based pairing j with 2*n-1-j is the same construction; the normalization, positivity and strict order are internal section assumptions
--   - encoding: Algorithm 1 with an arbitrary maximizing-agent choice, cheapest-bundle choices and two uniform random choices → the explicit recursive weighted list algorithm1 with index tie breaking, plus concluded probability normalization and completeness; reason: every chosen action obeys the algorithm, the full-completion permutations enumerate the residual bijections exactly once, and no cost bound is an input certificate
--   - encoding: round the actual Algorithm 1 fractional lottery while retaining assigned fixed bundles → a joint law of the Algorithm 1 support index and a tail-slot assignment, preserving the index and conditional slot marginals; reason: the additional witness records the stated rounding construction using the general Section 3.3 argument; it does not assume the frozen specialized Lemma 3.3 applies to new data
--   - encoding: finite agents, chores, complete partitions and finite lotteries → zero-based Fin labels, owner maps and published finite real-weight laws with positive-weight support; reason: bijections cover exactly the finite source instances, and repeated lottery atoms can be merged
--   - encoding: cost minimax share over all positive-part-count labelled partitions → the published costShare, the negative of the goods maximin functional on negative additive costs; reason: finite sign duality gives the same attained minimax without imposing any goods nonnegativity predicate
-- source:
--   Zehan Lin, Xiaowei Wu, Shengwei Zhou, STOC 2027 submission #845 (October 2026), Lemma 4.3, printed p. 16 / PDF p. 17. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/845.pdf

import Mathlib
import Definitions.Def_SublinearChoresMMS_Disposal_Supplement_TailRounding

noncomputable section

namespace SublinearChoresMMS.Disposal.Supplement

attribute [local instance] Classical.propDecidable

/-- Lemma 4.3, printed 16 / PDF 17. The joint law keeps the actual Algorithm 1
outcome and its rounded tail matching. Both fairness clauses and the exact
fixed-pair-or-tail-removal conclusion refer to this same law. -/
theorem lemma_4_3 (n m : ℕ) (hn : 0 < n) (hm : 2 * n ≤ m)
    (c : Cost n m) (hc : Normalized c) :
    ∃ F : FiniteLaw (Completion n),
      F.toLaw = algorithm1 c (oppositePairs n m) (oppositeTail n m) ∧
      ∃ P : FiniteLaw (Fin F.size × SlotAssignment n m),
        (∀ b, P.mean (fun o => if o.1 = b then 1 else 0) = F.weight b) ∧
        (∀ b e, e ∈ oppositeTail n m → ∀ s : Slots n m,
          P.mean (fun o => if o.1 = b ∧ o.2 e = s then 1 else 0) =
            F.weight b * tailSlot (oppositeTail n m) (F.atom b) s e) ∧
        (∀ i, P.mean (fun o => cost c i (bundle (fun e => (o.2 e).1) i)) ≤ propShare c i) ∧
        ∀ a, 0 < P.weight a →
          RoundsTail (oppositePairs n m) (oppositeTail n m)
            (F.atom (P.atom a).1) (P.atom a).2 ∧
          ∀ i,
            MMS1 c i (bundle (fun e => ((P.atom a).2 e).1) i) ∧
            (bundle (fun e => ((P.atom a).2 e).1) i =
              assignedBundle (oppositePairs n m) (F.atom (P.atom a).1) i ∨
            ∃ e ∈ bundle (fun e => ((P.atom a).2 e).1) i,
              e ∈ oppositeTail n m ∧
              cost c i ((bundle (fun e => ((P.atom a).2 e).1) i).erase e) ≤ propShare c i) := by sorry

end SublinearChoresMMS.Disposal.Supplement
