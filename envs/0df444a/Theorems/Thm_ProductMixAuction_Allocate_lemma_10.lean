-- Prove2me | Theorems.Thm_ProductMixAuction_Allocate_lemma_10
-- name    : ProductMixAuction.Allocate.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:18.284998+00:00
-- url     : https://prove2.me/theorems/0380a531-03fd-4bd2-8b78-2c1ee74553e6
-- title:
--   Lemma 10 (corrected: a path is closed when its last vertex has an earlier non-consecutive neighbour; time bound not modelled), p. 18 — FindParams' outputs
-- statement:
--   Let $\mathcal A$ be problem data $[p,(\mathcal B^j),(m^j),r]$ (not necessarily an allocation problem) whose marginal bids graph $G_{\mathcal A}$ has at least one edge. Consider the outputs of FindParams (Algorithm 2): an isolated demand cluster of the derived graph $D_{\mathcal A}$ if there is one; otherwise, for a maximal path $\pi_1,\dots,\pi_k$ of $D_{\mathcal A}$ starting at a link good, with last link good $i^*$ and last demand cluster $(I,j^*)$, the pair $(i^*,j^*)$ if the path is closed and the cluster $(I,j^*)$ if it is open. Then FindParams has at least one output, and every output is
--
--   1. a demand cluster $(I,j^*)$ with no link goods,
--   2. a demand cluster $(I,j^*)$ with one link good $i^*$, or
--   3. a cycle-link good $i^*$ together with the label $j^*$ of one of its incident edges in a multi-bidder cycle.
--
--   Here a path is *closed* when its last vertex $\pi_k$ is adjacent to some $\pi_s$ with $s\le k-2$.
--
--   This is the contract the main loop relies on: whichever walk FindParams takes, its output is a valid input to UnambiguousMarginals or to ShiftProjectUnshift.
--
--   Differences from the source:
--   - correction: a path is closed if there is an edge between v₁ and v_k (p. 18) → closed iff the last vertex is adjacent to an earlier vertex other than its predecessor; reason: with the printed definition the lemma is false: n = 3, p = 0, bidders 1–4 with single bids (5,5,0;+1), (0,5,5;+1), (0,5,5;+1), (0,−1,−1;+1) (all valid, t = (1,1,1) demanded); the maximal walk 1, C₁, 2, C₂, 3, C₃ is literally open, and FindParams would return C₃ = ({2,3}, 3), which has two link goods. The proof's 'consider only the cycle formed' uses the corrected notion
--   - encoding: In time O(α(n)n|ℬ|) → no running-time clause; reason: no machine model is formalized
--   - generalization: FindParams applied to an allocation problem → any problem data with at least one edge in G_A; reason: the statement does not use the allocation-problem conditions; allocation problems with an edge are instances
-- source:
--   Baldwin, Goldberg, Klemperer, Lock, Solving Strong-Substitutes Product-Mix Auctions, arXiv:1909.07313v3, p. 18, Lemma 10, Algorithm 2

import Mathlib
import Definitions.Def_ProductMixAuction_Allocate_Algorithm

namespace ProductMixAuction.Allocate

theorem lemma_10 {n : ℕ} {J : Type*} [Fintype J] [DecidableEq J] (A : AllocProblem n J)
    (hedge : (edges A).Nonempty) :
    (∃ c, FindParamsOutput A c) ∧ ∀ c, FindParamsOutput A c → AdmissibleChoice A c := by sorry

end ProductMixAuction.Allocate
