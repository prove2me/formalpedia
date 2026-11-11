-- Prove2me | Theorems.Thm_RandModSubsetSum_lemma_4_6
-- name    : RandModSubsetSum.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:01:14.78021+00:00
-- url     : https://prove2.me/theorems/c5348c19-6850-498f-92fc-4be705615860
-- title:
--   Lemma 4.6 — a fixed sibling pair is retained with probability $\ge1-(N_{\rm blk}+1)e^{-n^2}$
-- statement:
--   Fix a join of RepresentationSearch and process all $\nu_{j,v}=\lceil n^2/p^{\rm part}_{j,v}\rceil$ coordinate partitions and, at each block $B_h$, $T_h=\lceil n^2/p^{\rm tag}_h\rceil$ tag trials per branch, without time or space limits. Fix a sibling pair $(u,v)$ having the prescribed sibling type in every stratum before the partitions and tags are chosen. Then
--
--   $$\Pr\big[\text{both words occur in a common pair of lists emitted by TagFilter}\big]\ge1-(N_{\rm blk}+1)e^{-n^2}.$$
--
--   Repeated over the $127$ joins, this gives the factor $127(N_{\rm blk}+1)e^{-n^2}$ of Corollary 4.7.
--
--   **Formalization Note** The join is the abstract model of the definition `TagJoin`, with arbitrary consistent prescribed counts; $n=\sum_rn_r$.
--
--   Differences from the source:
--   - reading: a join (j, v) of RepresentationSearch processed by TagFilter (Algorithm 5) → the abstract join model JoinData: uniform partitions, fresh tag words uniform in their type classes for every trial of every branch; reason: the lemma concerns only the join's partitions and tags; the lists enter only through the fixed pair
--   - reading: both words occur in a common pair of lists emitted by TagFilter → some partition retains both words and some sequence of trials i_h ≤ T_h passes both marginal tag tests at every block; reason: a branch continues while both of its lists are nonempty, so this is the path event
--   - generalization: 13 strata, N_blk = 64, 40 tags, the types of SubblockTypes (Algorithm 4) → arbitrary strata, alphabets, tag alphabet, N_blk and consistent prescribed counts; reason: the proof uses only consistency; the paper's join is a special case
-- source:
--   Kim, Kim, Lee, Faster Provable Algorithm For Random Modular Subset Sum, STOC 2027 submission manuscript (sha256 c37a38c7…f89), Lemma 4.6, p. 27; (17)–(20), pp. 26–27

import Mathlib
import Definitions.Def_RandModSubsetSum_TagJoin

open scoped BigOperators

namespace RandModSubsetSum

/-- **Lemma 4.6** (retaining a fixed sibling pair). Kim, Kim, Lee, *Faster Provable Algorithm For Random Modular Subset Sum*, STOC 2027 submission
manuscript (sha256 c37a38c7…f89), Lemma 4.6, p. 27, with (17)–(20),
pp. 26–27.

Fix a join and process all `ν_{j,v} = ⌈n²/p^part_{j,v}⌉` coordinate partitions and, at each block,
`T_h = ⌈n²/p^tag_h⌉` tag trials per branch, without resource limits. Fix a sibling pair `(u, v)`
with the prescribed sibling type in every stratum before the partitions and tags are chosen. Then
both words occur in a common pair of lists emitted by TagFilter with probability at least
`1 − (N_blk + 1) e^{−n²}`.

**Formalization Note.** The join is the abstract model `JoinData`: arbitrary strata, alphabets,
tag alphabet and number of blocks, and consistent prescribed counts (the paper has 13 strata,
`N_blk = 64`, 40 tags, and the types of SubblockTypes, Algorithm 4). The randomness is uniform on
`JoinData.space` (independent uniform partitions; fresh tag words uniform in their type classes
for every trial of every branch). The event is `JoinData.Retained`: some partition retains both
words by the subblock marginal tests, and some sequence of trials passes both marginal tag tests on
every block. `n = Σ_r n_r`. -/
theorem lemma_4_6 {ι α S : Type} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    [Fintype S] [DecidableEq S] [Inhabited S]
    (J : JoinData ι α S) (hJ : J.Consistent) (u v : (r : ι) → Fin (J.nr r) → α)
    (huv : ∀ r ab, (Finset.univ.filter (fun c => (u r c, v r c) = ab)).card = J.G r ab) :
    1 - ((J.Nb : ℝ) + 1) * Real.exp (-((J.len : ℝ) ^ 2)) ≤ J.retainProb u v := by sorry

end RandModSubsetSum
