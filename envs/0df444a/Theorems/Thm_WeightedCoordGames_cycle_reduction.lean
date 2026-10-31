-- Prove2me | Theorems.Thm_WeightedCoordGames_cycle_reduction
-- name    : WeightedCoordGames.cycle_reduction
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:26:45.799987+00:00
-- url     : https://prove2.me/theorems/098a60df-e18a-4ac4-9b50-fea07bac9dd8
-- title:
--   §5, p.16 — a cycle of an open chain is a simple cycle with link bonuses $\beta^s_j$; its improvement paths lift to the chain
-- statement:
--   Fix a coordination game on an open chain $\mathcal C_1,\dots,\mathcal C_m$ with non-empty colour sets, a joint strategy $s$ and a cycle $\mathcal C_j$. Let $\beta^s_j$ be the link bonus (a link node $u$ of $\mathcal C_j$ gets bonus $1$ for the colour that $s$ gives its predecessor in the adjacent cycle).
--
--   1. For every joint strategy $t$ that agrees with $s$ outside $\mathcal C_j$ and every node $u$ of $\mathcal C_j$,
--   $$
--   p^{\text{chain}}_u(t)=p^{\mathcal C_j,\beta^s_j}_u(t|_{\mathcal C_j}),
--   $$
--   where the right-hand side is the payoff in the coordination game on the cycle $\mathcal C_j$ with bonus $\beta^s_j$.
--   2. Consequently, to every finite sequence $\chi=(\hat s=\chi_0\to\chi_1\to\dots\to\chi_L)$ of improvement steps of the game on $\mathcal C_j$ with bonus $\beta^s_j$ that starts at the restriction $\hat s$ of $s$ corresponds the sequence $\bar\chi$ of lifts (nodes of $\mathcal C_j$ play $\chi_k$, the other nodes keep $s$). This sequence starts at $s$, and every step of it is an improvement step of the chain game, so it is an initial segment of an improvement path of the chain game.
--
--   This reduction is what lets Algorithm 1 repair one cycle of the chain at a time using the constructions of Theorems 3 and 7.
--
--   **Formalization Note** Cycle positions are 0-based.
--
--   Differences from the source:
--   - generalization: the source states only the correspondence $\chi\mapsto\bar\chi$ → the payoff identity (clause 1) is stated as well; reason: clause 1 is the justification the paper gives in the same paragraph ("the edge to a link node u from another cycle can be regarded as a bonus of 1"), and clause 2 is the source's sentence
--   - reading: "the node $v$ belongs to $\mathcal C_{j-1}$ or to $\mathcal C_{j+1}$ and $v\to u$ is an edge" → $v$ is not a node of $\mathcal C_j$ and $v\to u$ is an edge; reason: the bonus models the edge "from another cycle"; in an open chain the two readings name the same predecessor, except that the literal one would also count the in-cycle edge $[j,1]\to[j,2]$ when $[j,2]$ is a link node, which the paper does not intend
--   - encoding: "a unique initial segment $\bar\chi$ of an improvement path" → the lifted sequence starts at $s$ and consists of improvement steps; reason: uniqueness holds by construction (the lift is a function of $\chi$); an initial segment of an improvement path is a finite sequence of improvement steps
-- source:
--   Apt–Simon–Wojtczak, Coordination Games on Weighted Directed Graphs, arXiv:1910.02693v2 (preprint), §5, p.16, paragraph and display defining β^s_j and the following sentence ("Further, to each improvement path χ …")

import Mathlib
import Definitions.Def_WeightedCoordGames_Model
import Definitions.Def_WeightedCoordGames_Algorithm

namespace WeightedCoordGames

/-- **A cycle of the chain is a cycle game with link bonuses** (Apt–Simon–Wojtczak,
arXiv:1910.02693v2, §5, p.16, the paragraph defining `β^s_j` and the sentence after it).

Fix a coordination game on an open chain, a joint strategy `s` and a cycle `C_j`.
1. For every joint strategy `t` that agrees with `s` outside `C_j`, every node `[j,i]` of `C_j` has the same
   payoff in `t` in the chain game as position `i` has in `t|C_j` in the coordination game on
   `C_j` with bonus `β^s_j`.
2. Consequently, to each finite sequence `χ` of improvement steps of the game on `C_j` with bonus
   `β^s_j` that starts at `ŝ = s|C_j` corresponds the sequence `χ̄` of its lifts (nodes of `C_j`
   play `χ`, the others keep `s`), which starts at `s` and is a sequence of improvement steps of
   the chain game, i.e. an initial segment of an improvement path. -/
theorem cycle_reduction {V M : Type*} [Fintype V] [DecidableEq V] [Fintype M] [DecidableEq M]
    {m v : ℕ} (O : OpenChain V m v) (C : V → Finset M) (hC : ∀ u, (C u).Nonempty)
    (s : V → M) (hs : (chainGame O C).toGame.IsJoint s) (j : Fin m) :
    (∀ t : V → M, (chainGame O C).toGame.IsJoint t → (∀ u, ¬ O.OnCycle j u → t u = s u) →
      ∀ i : Fin v, (chainGame O C).payoff (O.node j i) t =
        (O.cycleGameAt C s j).payoff i (O.restrict t j)) ∧
    (∀ (L : ℕ) (χ : Fin (L + 1) → Fin v → M), χ 0 = O.restrict s j →
      (∀ k : Fin L, (O.cycleGameAt C s j).toGame.ImprovStep (χ k.castSucc) (χ k.succ)) →
        O.lift s j (χ 0) = s ∧
          ∀ k : Fin L, (chainGame O C).toGame.ImprovStep
            (O.lift s j (χ k.castSucc)) (O.lift s j (χ k.succ))) := by sorry

end WeightedCoordGames
