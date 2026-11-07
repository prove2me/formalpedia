-- Prove2me | Theorems.Thm_ShortBroadcastDom_theorem_6_1_initial_cover
-- name    : ShortBroadcastDom.theorem_6_1_initial_cover
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:27:28.412882+00:00
-- url     : https://prove2.me/theorems/498fcaba-073a-4ca5-9402-63e7df5140b1
-- title:
--   Theorem 6.1 — a constant-round initial cover $D_0$ with $|D_0|\le A_a\tau_{R,c}(G)$ for all costs $c\ge1$
-- statement:
--   For every fixed $a\ge1$ there are a constant $A_a$ and a deterministic broadcast CONGEST algorithm with a constant number $T$ of rounds, whose local input is a demand bit, with the following property. On every finite graph $G\in\mathcal C_a$ with distinct identifiers of $O(\log(n+1))$ bits and demand set $R$ (the vertices whose bit is set), using messages of $O(\log(n+1))$ bits, it returns a set $D_0\subseteq V(G)$ such that
--
--   $$
--   R\subseteq N_G[D_0]\qquad\text{and}\qquad |D_0|\le A_a\,\tau_{R,c}(G)\ \text{ for every choice of costs } c_v\ge 1 .
--   $$
--
--   The algorithm does not use the costs and needs no orientation, embedding, decomposition, initial solution or knowledge of $n$. Its output organizes the fractional solver of Theorem 6.13.
--
--   **Formalization Note** The constant $A_a$, the algorithm and $T$ are chosen first; for every identifier exponent $k$ (identifiers below $(n+1)^k$) there is a message constant $c$ (messages of at most $c(\lfloor\log_2n\rfloor+1)$ bits) valid for all graphs.
--
--   Differences from the source:
--   - reading: broadcast CONGEST (messages received from each neighbour) → the multiset of the neighbours' messages, no port numbers; reason: gives the algorithm less information, so the existence statement is at least as strong; a sender can prepend its O(log(n+1))-bit identifier
--   - reading: O_a(1) rounds and O(log(n+1))-bit identifiers and messages → ∃ algorithm ∃ T, ∀ k ∃ c: identifiers < (n+1)^k, messages ≤ c(⌊log₂ n⌋+1) bits; reason: the algorithm and its round count do not depend on the identifier constant; this is the stronger order
--   - generalization: costs c_v ≥ 1 (τ_{R,c} defined in (1) with integer costs) → all real costs c_v ≥ 1; reason: integer costs are a special case; Corollary 6.11, used for the bound, holds for real costs
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), §6.1, p.23 (PDF p.26), Theorem 6.1

import Mathlib
import Definitions.Def_ShortBroadcastDom_InClassC
import Definitions.Def_ShortBroadcastDom_tauOn
import Definitions.Def_ShortBroadcastDom_BroadcastAlg

namespace ShortBroadcastDom

/-- **Theorem 6.1 (constant-round initial cover).** Amiri, Siebertz, Wawrzyniak, *Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix
f4dc98d2), §6.1, p.23 (PDF 26): "For every fixed
a ≥ 1, there exist a constant Aa and a deterministic broadcast CONGEST algorithm with the following
property. Given a graph G of minor density at most a and a locally specified set R ⊆ V(G), the
algorithm returns D0 ⊆ V(G) such that R ⊆ NG[D0], |D0| ≤ Aa τR,c(G) for every choice of costs
cv ≥ 1. The algorithm requires Oa(1) rounds, does not use the costs, and does not need an
orientation, embedding, decomposition, initial solution, or the number of vertices as input."

**Formalization Note** The local input of a vertex is only its demand bit; the output bit says
whether it is in `D₀`. The constant `A_a`, the algorithm and its round count `T` are chosen before
everything else; the identifier exponent `k` (identifiers `< (n+1)^k`) only affects the message
constant `c`. The costs are quantified after the output, as real numbers `≥ 1`. -/
theorem theorem_6_1_initial_cover (a : ℝ) (ha : 1 ≤ a) :
    ∃ Aa : ℝ, ∃ alg : BroadcastAlg Bool Bool, ∃ T : ℕ, ∀ k : ℕ, ∃ c : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (id : V → ℕ) (dem : V → Bool),
        ValidIds k (Fintype.card V) id → InClassC a G →
          MsgBounded alg G id dem T c (Fintype.card V) ∧
          DominatesSet G (Finset.univ.filter fun v => dem v = true) (alg.outSet G id dem T) ∧
          ∀ cost : V → ℝ, (∀ v, 1 ≤ cost v) →
            ((alg.outSet G id dem T).card : ℝ) ≤
              Aa * tau G (Finset.univ.filter fun v => dem v = true) cost := by sorry

end ShortBroadcastDom
