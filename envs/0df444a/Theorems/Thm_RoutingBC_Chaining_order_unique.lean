-- Prove2me | Theorems.Thm_RoutingBC_Chaining_order_unique
-- name    : RoutingBC.Chaining.order_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:43:51.121958+00:00
-- url     : https://prove2.me/theorems/f9210296-7697-4605-b46a-80ff872aabcf
-- title:
--   Proposition 1 — at most one order of a node set is traversed with positive probability
-- statement:
--   Let $R$ be a loop-free routing scheme on a finite node set $V$ (nonnegative, total forwarding probability one at every non-target node, the target forwarding nothing), whose decisions may depend on both the source $s$ and the target $t$. Fix $s,t\in V$, a set of nodes $M\subseteq V$, and two orderings $L_1$ and $L_2$ of $M$ (each lists every element of $M$ exactly once). If
--   $$\tilde\delta_{s,t}(L_1)>0\quad\text{and}\quad\tilde\delta_{s,t}(L_2)>0,$$
--   then $L_1=L_2$. Here $\tilde\delta_{s,t}(L)$ is the probability that a packet from $s$ to $t$ passes through the nodes of $L$ in the order of $L$.
--
--   In words: a packet from $s$ to $t$ can traverse a given set of nodes in at most one order with positive probability. The paper uses this to make the order of $s, s_1,\dots,s_k, t$ well defined in the proof of Lemma 1.
--
--   **Formalization Note.** The set $M$ and its two permutations are encoded as two repetition-free lists that are permutations of each other. The sentence before the proposition (p. 14) says "$\tilde\delta_{s,t}(L)\ge 0$"; the proposition itself has $>0$, which is what is stated. Source-obliviousness is not assumed. Total forwarding probability one and the silent target are the mission's standing assumptions (see the definitions file).
-- source:
--   Dolev, Elovici, Puzis, Routing Betweenness Centrality, BGU CS Tech. Rep. #2009-09 (Aug. 2009), Proposition 1, p. 14

import Mathlib
import Definitions.Def_RoutingBC_Chaining_Routing

namespace RoutingBC.Chaining

theorem order_unique {V : Type*} [Fintype V] [DecidableEq V]
    (R : V → V → V → V → ℝ) (hR : IsRoutingScheme R) (s t : V) (L₁ L₂ : List V)
    (h₁ : L₁.Nodup) (h₂ : L₂.Nodup) (hperm : L₁.Perm L₂)
    (hpos₁ : 0 < seqDelta R s t L₁) (hpos₂ : 0 < seqDelta R s t L₂) :
    L₁ = L₂ := by sorry

end RoutingBC.Chaining
