-- Prove2me | Theorems.Thm_WeightedCoordGames_lemma_10
-- name    : WeightedCoordGames.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:25:59.487978+00:00
-- url     : https://prove2.me/theorems/5f90f1cc-459d-4d81-9299-dde357e98963
-- title:
--   Lemma 10 — on open chains, and on simple cycles with unit bonuses, a node with payoff $\ge 1$ plays a best response
-- statement:
--   1. Consider a coordination game on an open chain (non-empty colour sets) and a joint strategy $s$. Every node $u$ with
--   $$
--   p_u(s)\ge 1
--   $$
--   plays a best response in $s$.
--   2. The same holds for coordination games on a simple cycle $1\to\dots\to n\to1$ ($n\ge2$, unweighted) in which each node has at most one bonus equal to $1$ and all its other bonuses are $0$: every node with payoff at least $1$ plays a best response.
--
--   The lemma says that a node with payoff $1$ can never improve, because a payoff of $2$ would need its two possible sources of payoff (two predecessors, or a predecessor and a unit bonus) to agree. It is used to show that the link nodes that hold a cycle's grade in place are never moved by Algorithm 1.
--
--   Differences from the source:
--   - reading: "coordination games on a simple cycle" → the unweighted simple cycle ($w=1$) with $n\ge2$ nodes; reason: by §3 (p.9) "simple cycle" without "weighted" is unweighted, and the proof's step "the only possibility … to get payoff 2 is if both of these colours coincide" needs unit weights; $n>1$ is the standing assumption of §2
-- source:
--   Apt–Simon–Wojtczak, Coordination Games on Weighted Directed Graphs, arXiv:1910.02693v2 (preprint), §5, Lemma 10, p.16

import Mathlib
import Definitions.Def_WeightedCoordGames_Model

namespace WeightedCoordGames

/-- **Lemma 10** (Apt–Simon–Wojtczak, arXiv:1910.02693v2, §5, p.16).
1. In a coordination game on an open chain, for every joint strategy `s`, each node with payoff
   `≥ 1` in `s` plays a best response.
2. The same holds for coordination games on a simple cycle (unweighted, `n ≥ 2` nodes) in which
   each node has at most one bonus equal to `1` and all its other bonuses are `0`.

**Formalization Note.** The cycle of clause 2 is unweighted, as "simple cycle" without
"weighted" means in the paper (§3, p.9). -/
theorem lemma_10 {M : Type*} [Fintype M] [DecidableEq M] :
    (∀ (V : Type*) [Fintype V] [DecidableEq V] {m v : ℕ} (O : OpenChain V m v)
      (C : V → Finset M), (∀ u, (C u).Nonempty) →
      ∀ (s : V → M) (u : V), (chainGame O C).toGame.IsJoint s →
        1 ≤ (chainGame O C).payoff u s → (chainGame O C).toGame.PlaysBR u s) ∧
    (∀ (n : ℕ), 2 ≤ n → ∀ (β : Fin n → M → ℕ),
      (∀ i c, β i c = 0 ∨ (β i c = 1 ∧ ∀ c', c' ≠ c → β i c' = 0)) →
      ∀ Cc : Fin n → Finset M, (∀ i, (Cc i).Nonempty) →
      ∀ (s : Fin n → M) (i : Fin n), (cycleGame n (fun _ _ => 1) β Cc).toGame.IsJoint s →
        1 ≤ (cycleGame n (fun _ _ => 1) β Cc).payoff i s →
          (cycleGame n (fun _ _ => 1) β Cc).toGame.PlaysBR i s) := by sorry

end WeightedCoordGames
