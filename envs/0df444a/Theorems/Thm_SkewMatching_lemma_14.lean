-- Prove2me | Theorems.Thm_SkewMatching_lemma_14
-- name    : SkewMatching.lemma_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:13:32.310707+00:00
-- url     : https://prove2.me/theorems/337390b1-b9fd-4a2e-b0a6-a98bdcc66511
-- title:
--   Lemma 14 — with probability 1 − O(n³ log(2U)/√U), no variable exceeds U
-- statement:
--   There is an absolute constant $c>0$ such that the following holds. Let $G$ be a simple skew-symmetric graph on $n\ge 1$ vertices, $s$ a source, $K\ge 1$, $U\ge 1$, and let $f^*$ be a maximum integral symmetric flow with $|f^*|\ge K$. Then for every reachability policy and every time $t$, the algorithm of §3.3 has failed by time $t$ with probability at most
--
--   $$
--   \frac{c\,n^3\log(2U)}{\sqrt U}.
--   $$
--
--   Choosing $U$ a large polynomial in $n$ gives success with high probability. Failure is the event that a variable $x_e$ exceeds $U$, which is the only way the algorithm can stop before finding its flow.
--
--   Differences from the source:
--   - generalization: the regular reachability algorithm of [GK96] → every ReachPolicy, a deterministic map obeying Lemma 23; reason: the paper's search is one policy; the supermartingale argument applies Lemma 15 to whichever barrier the policy returns
--   - reading: all edge variables will not exceed U throughout the algorithm → the absorbing status failed has probability at most the bound after every t; reason: failed is set the moment a variable exceeds U and it stays, so the events increase with t and this bounds their union
--   - reading: simple: no parallel edges between any two vertices → Simple: (tail, head) is injective, so antiparallel pairs and loops are allowed; reason: the wording of p.1 read per ordered pair; §2.3 says the algorithm also handles a constant number of parallel edges, and loops carry only cycle flow
--   - encoding: O(n³ log(2U)/√U) → c n³ log(2U)/√U with an absolute c, for every U ≥ 1 and n ≥ 1; reason: the printed O(·), with a constant before the graph
--   - encoding: a parameter K → K a natural number with K ≥ 1; reason: K is a positive parameter throughout the paper ("2n/K", "K/2"); at K = 0 Lemma 15 fails and the process need not ever find a negative edge
-- source:
--   Li, Li, Zhang, Maximum Cardinality Matching in n^{2+o(1)} Time, STOC 2027 submission (manuscript sha256 3fc151f5…), Lemma 14, p.9

import Mathlib
import Definitions.Def_SkewMatching_ProcState

namespace SkewMatching

/-- **Lemma 14**, p.9. "Let f* be a maximum integral symmetric flow in G. Suppose that |f*| ≥ K. With probability at least 1 − O(n³ log(2U)/√U), all edge variables x_e will not exceed U throughout the algorithm in Lemma 11."

Li, Li, Zhang, *Maximum Cardinality Matching in n^{2+o(1)} Time*, STOC 2027 submission (manuscript sha256 3fc151f5…), Lemma 14, p.9.

**Formalization Note.** `failed` is the status set the moment a variable exceeds `U` and it is absorbing, so its probability after `t` steps, for every `t`, bounds the probability that the algorithm ever fails. The constant is absolute and comes before the graph. The process is the algorithm of §3.3 run from its start, for every
reachability policy obeying Lemma 23 (the paper's search is one). The bound is for every `U ≥ 1` and is trivial when it exceeds `1`; the choice of `U` belongs to the goal's proof. -/
theorem lemma_14 :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ), 1 ≤ n → ∀ {E : Type} [Fintype E] (G : SkewGraph (Fin n) E),
      G.Simple → ∀ (s : Fin n) (K : ℕ), 1 ≤ K → ∀ (U : ℝ), 1 ≤ U → ∀ (π : ReachPolicy G s)
        (fstar : E → ℕ), G.IsMaxFlow s fstar → (K : ℤ) ≤ G.value s fstar → ∀ t : ℕ,
          (ProcState.law G s K U π t).toOuterMeasure {σ | σ.status = Status.failed} ≤
            ENNReal.ofReal (c * (n : ℝ) ^ 3 * Real.log (2 * U) / Real.sqrt U) := by sorry

end SkewMatching
