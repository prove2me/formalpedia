-- Prove2me | Theorems.Thm_RelativisticZK205_ThreeCol_comparators_step5
-- name    : RelativisticZK205.ThreeCol.comparators_step5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:17:40.666272+00:00
-- url     : https://prove2.me/theorems/974457dd-77b2-476e-af98-9ae856fe841d
-- title:
--   Step 5 — $z_{01}\neq z'_{01}\iff i=j'$, $z_{10}\neq z'_{10}\iff j=i'$, $z_{11}\neq z'_{11}\iff j=j'$
-- statement:
--   In the setting of Step 4 (two edge queries $((i,j),r)$ and $((i',j'),r')$, no abort), on every outcome of the PR-boxes the remaining three comparators give
--
--   $$
--   z_{01}\neq z'_{01}\iff i=j',\qquad z_{10}\neq z'_{10}\iff j=i',\qquad z_{11}\neq z'_{11}\iff j=j'.
--   $$
--
--   Together with Step 4, the simulators hold XOR-shares of all four vertex coincidences between the two queries.
--
--   Differences from the source:
--   - reading: Steps 4–5 are executed after Step 3 (where a simulator with a non-edge query aborts) → hypotheses that both queries are edges; reason: the claim concerns the bits computed by two simulators that have not aborted
--   - encoding: each vertex label written as an h-bit string, h = ⌈log₂|V|⌉, with k-th bit i_k → h = Nat.clog 2 n and i_k = Nat.testBit i (k − 1) (least significant bit first); reason: the source fixes no bit order; any injective h-bit encoding of the labels is the source's construction
--   - encoding: an identity between the bits the simulators compute → the identity on every outcome of positive probability (the support of the output law); reason: an identity of random bits holds surely; for a discrete law this is exactly the support
--   - encoding: a graph G on the labels 0, …, |V|−1, with query bits in F₂ → G : SimpleGraph (Fin n) with decidable adjacency, Query n := Fin n × Fin n × Bool; reason: Fin n is the source label set and Bool is its two-element query alphabet; finite adjacency admits a decision procedure
--   - encoding: (i, j) ∈ E, edges always represented with i < j → IsValid G (i, j, r) := i < j ∧ G.Adj i j; reason: the source's own convention for membership of an ordered pair in E (p.9)
-- source:
--   Claude Crépeau, Harmanpreet Singh Grover, April Niu, Nan Yang, Fadi Younes, Relativistic Zero Knowledge, STOC 2027 submission #205 (October 2026), p.10, Step 5; p.11 ("Similar proofs are not provided but essentially the same")

import Mathlib
import Definitions.Def_RelativisticZK205_ThreeCol_Simulator

namespace RelativisticZK205.ThreeCol

/-- Step 5, p.10: when neither simulator aborts, the other three comparators give
`z₀₁ ≠ z'₀₁ ⟺ i = j'`, `z₁₀ ≠ z'₁₀ ⟺ j = i'` and `z₁₁ ≠ z'₁₁ ⟺ j = j'`, on every outcome of positive
probability. -/
theorem comparators_step5 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (i j i' j' : Fin n) (r r' : Bool) (h₁ : IsValid G (i, j, r)) (h₂ : IsValid G (i', j', r')) :
    ∀ p ∈ (preprocess G (i, j, r) (i', j', r')).support,
      (p.1.2 false true ≠ p.2.2 false true ↔ i = j') ∧
      (p.1.2 true false ≠ p.2.2 true false ↔ j = i') ∧
      (p.1.2 true true ≠ p.2.2 true true ↔ j = j') := by sorry

end RelativisticZK205.ThreeCol
