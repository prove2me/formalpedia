-- Prove2me | Theorems.Thm_ShortBroadcastDom_Supplement_theorem_F_1
-- name    : ShortBroadcastDom.Supplement.theorem_F_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T23:45:00.086247+00:00
-- url     : https://prove2.me/theorems/563b05ae-2871-4d1b-aa11-8584a632fb1d
-- title:
--   Theorem F.1 — total dominating sets of size $\le 2a\,\gamma_{t,f}(G)$ in constant broadcast CONGEST rounds
-- statement:
--   There are deterministic broadcast CONGEST algorithms with a constant number of rounds that return, on an isolate-free graph $G$, a total dominating set $D$ with
--
--   $$
--   |D|\le 2a\,\gamma_{t,f}(G)
--   $$
--
--   in each of the following cases:
--
--   1. $G\in\mathcal C_a$, for every fixed rational $a\ge1$;
--   2. $G\in\mathcal C_\rho$ and every subgraph of $G$ has a ratio of edges to vertices of at most $a$, for fixed rationals $1\le a\le\rho$ with $2a\notin\mathbb Z$.
--
--   The coefficient is one smaller than the coefficient $2a+1$ for ordinary domination, because a demand is covered only by a neighbour.
--
--   **Formalization Note** Same algorithmic conventions as Theorem C: one algorithm and round count per parameter choice, before the identifier exponent and the graph; vertices know only their identifiers.
--
--   Differences from the source:
--   - reading: broadcast CONGEST (each vertex receives its neighbours' messages) → the multiset of the neighbours' messages, without port numbers; reason: gives the algorithm less information, so the existence statement is at least as strong; a sender can prepend its O(log(n+1))-bit identifier
--   - reading: constant-round, identifiers and messages of O(log(n+1)) bits → ∃ algorithm ∃ T, ∀ k ∃ c: identifiers < (n+1)^k, messages ≤ c(⌊log₂ n⌋+1) bits; reason: the algorithm and its round count are independent of the identifier constant k; this is the stronger quantifier order
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), App. F, p.77 (PDF p.80), Theorem F.1

import Mathlib
import Definitions.Def_ShortBroadcastDom_InClassC
import Definitions.Def_ShortBroadcastDom_SubgraphDensityLE
import Definitions.Def_ShortBroadcastDom_BroadcastAlg
import Definitions.Def_ShortBroadcastDom_Supplement_IsTotalDom

namespace ShortBroadcastDom.Supplement

open ShortBroadcastDom

/-- **Theorem F.1 (exact coefficient `2a` for total domination).** Amiri, Siebertz, Wawrzyniak,
*Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix f4dc98d2), App. F, p.77 (PDF 80):
"There are deterministic constant-round Congest-BC algorithms that return, on an isolate-free graph
G, a total dominating set D with |D| ≤ 2a γt,f(G) in each of the following cases. (i) G ∈ Ca, for
every fixed rational a ≥ 1. (ii) G ∈ Cρ and every subgraph of G has a ratio of edges to vertices of
at most a, for fixed rationals 1 ≤ a ≤ ρ such that 2a is not an integer."

**Formalization Note** One conjunct per case, in the shape of Theorem C: for the fixed parameters
one algorithm (local input `Unit`) and one round count `T`, before the identifier exponent `k` and
the graph; identifiers injective and `< (n + 1)^k`, messages of at most `c(⌊log₂ n⌋ + 1)` bits;
`D` is the set of vertices outputting `true` after `T` rounds. "Congest-BC" is the broadcast
CONGEST model (`BroadcastAlg`). -/
theorem theorem_F_1 :
    (∀ a : ℚ, 1 ≤ a →
      ∃ alg : BroadcastAlg Unit Bool, ∃ T : ℕ, ∀ k : ℕ, ∃ c : ℕ,
        ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
          (id : V → ℕ), ValidIds k (Fintype.card V) id → IsolateFree G → InClassC (a : ℝ) G →
            MsgBounded alg G id (fun _ => ()) T c (Fintype.card V) ∧
            IsTotalDom G (alg.outSet G id (fun _ => ()) T) ∧
            ((alg.outSet G id (fun _ => ()) T).card : ℝ) ≤ 2 * (a : ℝ) * totFracDom G) ∧
    (∀ a ρ : ℚ, 1 ≤ a → a ≤ ρ → (∀ m : ℤ, 2 * a ≠ m) →
      ∃ alg : BroadcastAlg Unit Bool, ∃ T : ℕ, ∀ k : ℕ, ∃ c : ℕ,
        ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
          (id : V → ℕ), ValidIds k (Fintype.card V) id → IsolateFree G → InClassC (ρ : ℝ) G →
            SubgraphDensityLE (a : ℝ) G →
            MsgBounded alg G id (fun _ => ()) T c (Fintype.card V) ∧
            IsTotalDom G (alg.outSet G id (fun _ => ()) T) ∧
            ((alg.outSet G id (fun _ => ()) T).card : ℝ) ≤ 2 * (a : ℝ) * totFracDom G) := by sorry

end ShortBroadcastDom.Supplement
