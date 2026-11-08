-- Prove2me | Theorems.Thm_SkewMatching_theorem_1
-- name    : SkewMatching.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:09:33.825122+00:00
-- url     : https://prove2.me/theorems/071d9bb2-b7e4-4b31-bf57-ba4be92c0174
-- title:
--   Theorem 1 — a maximum matching of a general graph in n^{2+o(1)} time with high probability
-- statement:
--   There is one program $P$ and one function $g(n)\to 0$ such that for every $C>0$ there is a constant $K>0$ with the following property. For every graph $G$ on $n$ vertices and every listing of its edges, the probability that $P$ fails to halt within
--
--   $$
--   \lceil K(n+2)^{2+g(n+2)}\rceil
--   $$
--
--   steps with the output encoding a maximum matching of $G$ is at most $(n+2)^{-C}$.
--
--   The graph is arbitrary: no assumption is made on its density, its connectivity, or the existence of a perfect matching.
--
--   **Formalization Note** The event is bounded as an outer measure of the fair-coin product measure on tapes, so no measurability needs to be proved in the statement.
--
--   Differences from the source:
--   - reading: we can compute → a Machine.Program, a unit-cost word RAM with coins and word bound (n+2)^wordExp; reason: the paper names no machine (paper.md decision 3)
--   - reading: n^{2+o(1)} time with high probability → ∃ g → 0 before C, a constant K after C, failure probability (n+2)^{−C} for arbitrary C; reason: the paper gives no order; this is the stronger one (paper.md decision 4)
--   - encoding: n → n+2 in the time and the failure probability; reason: n = 0, 1 would otherwise be vacuous or junk; implies the printed form for n ≥ 2 up to the constant
--   - encoding: an unweighted general graph G → a SimpleGraph on Fin n given as an edge list; reason: a SimpleGraph is loopless with no parallel edges; the paper fixes no input format and m ≤ n² keeps reading the list within budget
--   - encoding: compute a maximum matching of G → when halted, memory cell −1 holds ℓ and cells −2−2j, −3−2j hold the endpoints of the j-th of ℓ distinct edges that form a maximum matching of G (DecodesMaxMatching); reason: the paper fixes no output format
-- source:
--   Li, Li, Zhang, Maximum Cardinality Matching in n^{2+o(1)} Time, STOC 2027 submission (manuscript sha256 3fc151f5…), Theorem 1, p.1

import Mathlib
import Definitions.Def_SkewMatching_DecodesMaxMatching

namespace SkewMatching

open Filter Topology

/-- **Theorem 1**, p.1. "Given a unweighted general graph G with n vertices, we can compute a maximum matching of G in n^{2+o(1)} time with high probability."

Li, Li, Zhang, *Maximum Cardinality Matching in n^{2+o(1)} Time*, STOC 2027 submission (manuscript sha256 3fc151f5…), Theorem 1, p.1.

**Formalization Note.**
* There is one program `P` and one `g → 0`, before every `C > 0`, then `K`, then the instance: every `n`, every `SimpleGraph (Fin n)`, every listing of its edges. There is no hypothesis on density, connectivity, or a perfect matching.
* **Monte Carlo.** The theorem claims success with high probability: the event "not halted within `⌈K (n+2)^{2+g(n+2)}⌉` steps with a maximum matching decoded" has outer measure at most `(n+2)^{−C}`. No clause on wrong outputs is added.
* `n + 2` in the time and in the failure probability keeps `n = 0, 1` from being vacuous or junk, and implies the printed form for `n ≥ 2` up to the constant.
* The machine is `Machine.Program` with word bound `(n+2)^wordExp`, a unit-cost word RAM with coins (the paper names none). Input: `matchingMem`; output: `DecodesMaxMatching`. A `SimpleGraph` is loopless with no parallel edges, which is "unweighted general graph" here. -/
theorem theorem_1 :
    ∃ (P : Machine.Program) (g : ℕ → ℝ), Tendsto g atTop (𝓝 0) ∧
      ∀ C : ℝ, 0 < C → ∃ K : ℝ, 0 < K ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (el : List (Fin n × Fin n)), IsEdgeListing G el →
          let W := Machine.wordBound P (n + 2)
          let σ₀ := Machine.initState (matchingMem el)
          Machine.coinTape {τ | ¬ ∃ T ≤ ⌈K * ((n : ℝ) + 2) ^ (2 + g (n + 2))⌉₊,
              Machine.HaltsWithin P W τ σ₀ T ∧
                DecodesMaxMatching G (Machine.run P W τ σ₀ T).mem} ≤
            ENNReal.ofReal (((n : ℝ) + 2) ^ (-C)) := by sorry

end SkewMatching
