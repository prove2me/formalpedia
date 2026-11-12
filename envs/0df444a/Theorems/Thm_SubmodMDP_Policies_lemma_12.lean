-- Prove2me | Theorems.Thm_SubmodMDP_Policies_lemma_12
-- name    : SubmodMDP.Policies.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:12:49.410338+00:00
-- url     : https://prove2.me/theorems/a70ff000-018a-4c59-a40d-dd629cba7177
-- title:
--   Lemma 12 — Algorithm 4 never outputs "error"
-- statement:
--   Let $G$ be a layered MDP graph with $H=d^r$ ($d\ge2$, $r\ge1$), and let $x\in Q^{(r)}$ satisfy (7). Suppose $v_1,\dots,v_H$ are obtained by repeatedly applying Algorithm 4 on the previous vertices and $x$. Then the policy never outputs "error": for every $k<H$ and every trajectory $v_1,\dots,v_k$ that the process reaches with positive probability, Algorithm 4 returns a distribution.
--
--   Together with Lemma 11 this shows that Algorithm 4 defines a valid policy on the decision vertices.
--
--   Differences from the source:
--   - reading: the policy never outputs "error" → for every k < H and every trajectory of length k with positive probability under the repeated process, alg4 ≠ none; reason: "never" for a randomized process means on every reachable trajectory
--   - encoding: sampling v_{ℓ+1} from the output of Algorithm 4 → the formal process fails (none) if the output weights are not a probability vector; reason: sampling is only defined for a probability vector; Lemma 13 shows this failure has probability 0
-- source:
--   Lars Rohwedder, Rico Zenklusen, STOC 2027 submission #658 (October 2026), Lemma 12, p. 19 (PDF p. 20)

import Mathlib
import Definitions.Def_SubmodMDP_Policies_GraphMDP

namespace SubmodMDP.Policies

/-- Lemma 12 (PDF p. 19): for `x ∈ Q^(r)` satisfying (7), when `v₁, …, v_H` are obtained by
repeatedly applying Algorithm 4 on the previous vertices and `x`, Algorithm 4 never outputs
"error": on every trajectory `v₁, …, v_k` (`k < H`) reached with positive probability it returns
a weight vector. -/
theorem lemma_12 (M : GMDP) (hM : M.WF) (d r : ℕ) (hd : 2 ≤ d) (hr : 1 ≤ r)
    (hH : M.G.H = d ^ r) (x : Finset (Fin M.G.N) → ℝ) (hx : InQ M.G r x) (h7 : Sat7 M r x) :
    ∀ k < M.G.H, ∀ τ : List (Fin M.G.N), some τ ∈ (mdpPrefix M d x k).support →
      alg4 M d x τ ≠ none := by sorry

end SubmodMDP.Policies
