-- Prove2me | Theorems.Thm_ShortBroadcastDom_Supplement_theorem_9_1
-- name    : ShortBroadcastDom.Supplement.theorem_9_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T23:44:23.422759+00:00
-- url     : https://prove2.me/theorems/39312e8b-9ed9-41af-b930-23c3bbf9e68f
-- title:
--   Theorem 9.1 (= Theorem E) — dominating sets of size $\le 7\gamma(G)$ on every fixed surface in constant broadcast CONGEST rounds
-- statement:
--   For every fixed integer $e\ge0$ there is a deterministic broadcast CONGEST algorithm with a constant number of rounds that returns a dominating set $D$ with
--
--   $$
--   |D|\le7\,\gamma(G)
--   $$
--
--   on every graph $G$ of Euler genus at most $e$, where $\gamma(G)$ is the domination number. Messages have $O(\log n)$ bits; the algorithm needs no embedding, orientation, degree bound, initial cover or knowledge of $n$, and the statement covers orientable and non-orientable surfaces.
--
--   The benchmark is the integral optimum: on some fixed surfaces even a sequential algorithm cannot guarantee $7\gamma_f(G)$ (Proposition I.1), and seven is optimal already on planar graphs.
--
--   **Formalization Note** $|D|\le7|S|$ for every dominating set $S$. Euler genus at most $e$ is the published combinatorial definition (an embedding scheme, i.e. rotation system and edge signature, of Euler genus at most $e$). One algorithm and round count per $e$, before the identifier exponent and the graph.
--
--   Differences from the source:
--   - reading: broadcast CONGEST (each vertex receives its neighbours' messages) → the multiset of the neighbours' messages, without port numbers; reason: gives the algorithm less information, so the existence statement is at least as strong; a sender can prepend its O(log(n+1))-bit identifier
--   - reading: constant-round, identifiers and messages of O(log(n+1)) bits → ∃ algorithm ∃ T, ∀ k ∃ c: identifiers < (n+1)^k, messages ≤ c(⌊log₂ n⌋+1) bits; reason: the algorithm and its round count are independent of the identifier constant k; this is the stronger quantifier order
--   - encoding: Euler genus: least Euler genus of a closed surface in which the graph embeds → PlanarQueue.Genus.EulerGenusLE G e (an embedding scheme of Euler genus ≤ e, summed over components); reason: combinatorial embeddings correspond to cellular embeddings (Heffter–Edmonds–Ringel) and Euler genus is additive over components
--   - encoding: |D| ≤ 7γ(G) → |D| ≤ 7|S| for every dominating set S; reason: γ(G) is the minimum size of a dominating set
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), §9, p.50 (PDF p.53), Theorem 9.1; informal Theorem E, §1.4, p.5 (PDF p.8)

import Mathlib
import Definitions.Def_ShortBroadcastDom_closedNbhd
import Definitions.Def_ShortBroadcastDom_BroadcastAlg
import Definitions.Def_PlanarQueue_Genus_EulerGenus

namespace ShortBroadcastDom.Supplement

open ShortBroadcastDom

/-- **Theorem 9.1 (= Theorem E: exactly seven on every fixed surface).** Amiri, Siebertz,
Wawrzyniak, *Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix f4dc98d2), §9, p.50
(PDF 53): "For every fixed integer e ≥ 0, there is a deterministic constant-round broadcast CONGEST
algorithm that finds a dominating set D with |D| ≤ 7γ(G) on every graph G of Euler genus at most e.
The algorithm uses O(log n) bits per message. It needs no embedding, orientation, degree bound,
initial cover, or knowledge of n. The statement includes both orientable and non-orientable
surfaces." Informal version: Theorem E, §1.4, p.5 (PDF 8).

**Formalization Note** One algorithm `alg` (local input `Unit`) and round count `T` per `e`, chosen
before the identifier exponent `k` and the graph. The benchmark is the integral domination number:
`|D| ≤ 7|S|` for every dominating set `S` of `G`. Euler genus at most `e` is the published
`PlanarQueue.Genus.EulerGenusLE G e` (an embedding scheme, i.e. rotation system and edge signature,
of Euler genus `≤ e`, summed over components), which covers orientable and non-orientable
surfaces. -/
theorem theorem_9_1 (e : ℕ) :
    ∃ alg : BroadcastAlg Unit Bool, ∃ T : ℕ, ∀ k : ℕ, ∃ c : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (id : V → ℕ), ValidIds k (Fintype.card V) id → PlanarQueue.Genus.EulerGenusLE G e →
          MsgBounded alg G id (fun _ => ()) T c (Fintype.card V) ∧
          DominatesSet G Finset.univ (alg.outSet G id (fun _ => ()) T) ∧
          ∀ S : Finset V, DominatesSet G Finset.univ S →
            (alg.outSet G id (fun _ => ()) T).card ≤ 7 * S.card := by sorry

end ShortBroadcastDom.Supplement
