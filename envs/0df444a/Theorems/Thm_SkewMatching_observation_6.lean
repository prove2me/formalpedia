-- Prove2me | Theorems.Thm_SkewMatching_observation_6
-- name    : SkewMatching.observation_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:09:42.302263+00:00
-- url     : https://prove2.me/theorems/c6cb13e0-2e88-4ccf-bcc1-fe9c427d2e75
-- title:
--   Observation 6 — matchings of G and integral symmetric flows in M_G
-- statement:
--   Let $G$ be a graph on a finite vertex set and $M_G$ its matching graph.
--
--   1. Every matching $M$ of $G$ gives an integral symmetric flow $f$ in $M_G$ with $f(u,v')=1$ exactly when $\{u,v\}\in M$, and with value $2|M|$.
--   2. Conversely, for every integral symmetric flow $f$ in $M_G$, the set $M=\{\{u,v\}:f(u,v')=1\}$ is a matching of $G$, and $|f|=2|M|$.
--
--   Hence maximum flows correspond to maximum matchings, which is the reduction of Theorem 1 to Theorem 2.
--
--   Differences from the source:
--   - reading: conversely, any flow corresponds to a general matching → the matching is {u, v : f(u, v′) = 1}, and the value 2|M| is stated in the converse as well; reason: the proof pairs the paths s→u→v′→s′ with matching edges, and the reduction needs the value
-- source:
--   Li, Li, Zhang, Maximum Cardinality Matching in n^{2+o(1)} Time, STOC 2027 submission (manuscript sha256 3fc151f5…), Observation 6, p.3

import Mathlib
import Definitions.Def_SkewMatching_DecodesMaxMatching
import Definitions.Def_SkewMatching_SkewGraph_IsFlow
import Definitions.Def_SkewMatching_matchingGraph

namespace SkewMatching

/-- **Observation 6**, p.3. "Any general matching in the original graph G corresponds to an integral symmetric flow in the matching graph M_G whose flow value is twice the matching size. Conversely, any integral symmetric flow in M_G corresponds to a general matching in G."

Li, Li, Zhang, *Maximum Cardinality Matching in n^{2+o(1)} Time*, STOC 2027 submission (manuscript sha256 3fc151f5…), Observation 6, p.3.

**Formalization Note.** The correspondence is `{u, v} ∈ M ↔ f(u, v′) = 1`. The value `2 |M|` is stated in the converse as well: without it the observation would not give the reduction of Theorem 1 to Theorem 2. Finite `V`. -/
theorem observation_6 {V : Type*} [Fintype V] (G : SimpleGraph V) :
    (∀ M : Finset (Sym2 V), IsMatchingOf G M →
      ∃ f : MatchEdge G → ℕ, (matchingGraph G).IsFlow (matchingSource V) f ∧
        (∀ (u v : V) (h : G.Adj u v), f (.inl ⟨(u, v), h⟩) = 1 ↔ s(u, v) ∈ M) ∧
        (matchingGraph G).value (matchingSource V) f = 2 * (M.card : ℤ)) ∧
    ∀ f : MatchEdge G → ℕ, (matchingGraph G).IsFlow (matchingSource V) f →
      ∃ M : Finset (Sym2 V), IsMatchingOf G M ∧
        (∀ (u v : V) (h : G.Adj u v), f (.inl ⟨(u, v), h⟩) = 1 ↔ s(u, v) ∈ M) ∧
        (matchingGraph G).value (matchingSource V) f = 2 * (M.card : ℤ) := by sorry

end SkewMatching
