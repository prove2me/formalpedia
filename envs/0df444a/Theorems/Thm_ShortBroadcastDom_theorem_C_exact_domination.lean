-- Prove2me | Theorems.Thm_ShortBroadcastDom_theorem_C_exact_domination
-- name    : ShortBroadcastDom.theorem_C_exact_domination
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:27:34.649332+00:00
-- url     : https://prove2.me/theorems/04276ca9-388c-41fe-8d80-47349cd52cd6
-- title:
--   Theorem C — dominating sets of size $\le(2a+1)\gamma_f(G)$, resp. $(3+4/(g-2))\gamma_f(G)$, in constant broadcast CONGEST rounds
-- statement:
--   There are deterministic constant-round broadcast CONGEST algorithms that return a dominating set $D$ with the following guarantees. In each clause the algorithm and its number $T$ of rounds depend only on the fixed parameters; vertices have distinct identifiers of $O(\log(n+1))$ bits, every message has $O(\log(n+1))$ bits, and no vertex knows anything but its identifier (no embedding, orientation, initial cover, degree bound or knowledge of $n$).
--
--   1. For every fixed rational $a\ge1$ and every $G\in\mathcal C_a$:
--   $$|D|\le(2a+1)\,\gamma_f(G).$$
--   2. For all fixed rationals $1\le a\le\rho$ with $2a\notin\mathbb Z$, the same bound $|D|\le(2a+1)\gamma_f(G)$ holds for every $G\in\mathcal C_\rho$ all of whose subgraphs have density at most $a$.
--   3. For every fixed integer $g\ge3$ and every planar $G$ of girth at least $g$:
--   $$|D|\le\Bigl(3+\frac{4}{g-2}\Bigr)\gamma_f(G).$$
--
--   On planar graphs this gives $|D|\le7\gamma_f(G)$, and on triangle-free planar graphs $|D|\le5\gamma_f(G)$; these coefficients are optimal for deterministic constant-round algorithms.
--
--   **Formalization Note** For each clause: there exist an algorithm (local input `Unit`) and a round count $T$ such that for every identifier exponent $k$ there is a message constant $c$ with: on every finite graph of the class with injective identifiers below $(n+1)^k$, every message in the first $T$ rounds has at most $c(\lfloor\log_2n\rfloor+1)$ bits, the set $D$ of vertices outputting `true` after $T$ rounds dominates $G$, and $|D|$ obeys the bound. $\gamma_f$ is the LP minimum. Girth at least $g$ is $g\le\mathrm{egirth}$; planarity is the published plane-drawing definition.
--
--   Differences from the source:
--   - reading: broadcast CONGEST (each vertex receives its neighbours' messages) → the multiset of the neighbours' messages, without port numbers; reason: gives the algorithm less information, so the existence statement is at least as strong; a sender can prepend its O(log(n+1))-bit identifier
--   - reading: constant-round, identifiers and messages of O(log(n+1)) bits → ∃ algorithm ∃ T, ∀ k ∃ c: identifiers < (n+1)^k, messages ≤ c(⌊log₂ n⌋+1) bits; reason: the algorithm and its round count are independent of the identifier constant k; this is the stronger quantifier order
--   - encoding: girth at least g → g ≤ egirth (ℕ∞); reason: acyclic graphs have infinite girth, as in the paper
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), §1.2, p.3 (PDF p.6), Theorem C

import Mathlib
import Definitions.Def_ShortBroadcastDom_InClassC
import Definitions.Def_ShortBroadcastDom_SubgraphDensityLE
import Definitions.Def_ShortBroadcastDom_tauOn
import Definitions.Def_ShortBroadcastDom_BroadcastAlg
import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar

namespace ShortBroadcastDom

/-- **Theorem C (exact domination coefficients).** Amiri, Siebertz, Wawrzyniak, *Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix
f4dc98d2), §1.2, p.3 (PDF 6): "There exist
deterministic constant-round broadcast CONGEST algorithms that return a dominating set D with the
following guarantees. (i) For fixed rational a ≥ 1 and G ∈ Ca, the output satisfies
|D| ≤ (2a + 1)γf(G). (ii) For fixed rationals 1 ≤ a ≤ ρ with 2a noninteger, the same bound holds
for G ∈ Cρ if every subgraph has a ratio of edges to vertices of at most a. (iii) For planar G of
girth at least a fixed integer g ≥ 3, we have |D| ≤ (3 + 4/(g − 2))γf(G). The algorithms require no
embedding, orientation, initial cover, degree bound, or knowledge of n."

**Formalization Note** One conjunct per clause. In each, for the fixed parameters there is one
algorithm `alg` (local input `Unit`: a vertex knows only its identifier) and one round count `T`,
chosen before the identifier exponent `k` and before the graph; only the message constant `c` may
depend on `k`. Identifiers are distinct and `< (n+1)^k`; every message in the first `T` rounds has
at most `c(⌊log₂ n⌋ + 1)` bits; the output after exactly `T` rounds is the set `D` of vertices
outputting `true`. Girth at least `g` is `g ≤ egirth` in `ℕ∞`; planarity is the published
`RobertsonSeymour1986.GM5.IsPlanar`. -/
theorem theorem_C_exact_domination :
    (∀ a : ℚ, 1 ≤ a →
      ∃ alg : BroadcastAlg Unit Bool, ∃ T : ℕ, ∀ k : ℕ, ∃ c : ℕ,
        ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
          (id : V → ℕ), ValidIds k (Fintype.card V) id → InClassC (a : ℝ) G →
            MsgBounded alg G id (fun _ => ()) T c (Fintype.card V) ∧
            DominatesSet G Finset.univ (alg.outSet G id (fun _ => ()) T) ∧
            ((alg.outSet G id (fun _ => ()) T).card : ℝ) ≤ (2 * (a : ℝ) + 1) * fracDom G) ∧
    (∀ a ρ : ℚ, 1 ≤ a → a ≤ ρ → (∀ m : ℤ, 2 * a ≠ m) →
      ∃ alg : BroadcastAlg Unit Bool, ∃ T : ℕ, ∀ k : ℕ, ∃ c : ℕ,
        ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
          (id : V → ℕ), ValidIds k (Fintype.card V) id → InClassC (ρ : ℝ) G →
            SubgraphDensityLE (a : ℝ) G →
            MsgBounded alg G id (fun _ => ()) T c (Fintype.card V) ∧
            DominatesSet G Finset.univ (alg.outSet G id (fun _ => ()) T) ∧
            ((alg.outSet G id (fun _ => ()) T).card : ℝ) ≤ (2 * (a : ℝ) + 1) * fracDom G) ∧
    (∀ g : ℕ, 3 ≤ g →
      ∃ alg : BroadcastAlg Unit Bool, ∃ T : ℕ, ∀ k : ℕ, ∃ c : ℕ,
        ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
          (id : V → ℕ), ValidIds k (Fintype.card V) id → RobertsonSeymour1986.GM5.IsPlanar G →
            (g : ℕ∞) ≤ G.egirth →
            MsgBounded alg G id (fun _ => ()) T c (Fintype.card V) ∧
            DominatesSet G Finset.univ (alg.outSet G id (fun _ => ()) T) ∧
            ((alg.outSet G id (fun _ => ()) T).card : ℝ) ≤ (3 + 4 / ((g : ℝ) - 2)) * fracDom G) := by sorry

end ShortBroadcastDom
