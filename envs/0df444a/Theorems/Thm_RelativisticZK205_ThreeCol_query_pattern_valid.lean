-- Prove2me | Theorems.Thm_RelativisticZK205_ThreeCol_query_pattern_valid
-- name    : RelativisticZK205.ThreeCol.query_pattern_valid
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:17:43.298582+00:00
-- url     : https://prove2.me/theorems/10b8623b-9aa9-4b36-9ba3-9c1b4e210c1a
-- title:
--   Fig. 10 — the simulators' comparison bits satisfy the 3-COLZK input condition
-- statement:
--   For two edge queries $((i,j),r)$ and $((i',j'),r')$ (so $i<j$ and $i'<j'$), on every outcome of the preprocessing the bits $m_{uv}=z_{uv}\oplus z'_{uv}$ satisfy the condition of Fig. 10 that each vertex matches at most one vertex on the other side:
--
--   $$
--   \forall u,v\in\{0,1\},\quad m_{uv}\,m_{u\bar v}=m_{uv}\,m_{\bar uv}=0.
--   $$
--
--   Hence in Step 6 the 3-COLZK channel is always in its constrained regime.
--
--   Differences from the source:
--   - reading: Fig. 10 states the condition on 3-COLZK's inputs and the simulators invoke 3-COLZK in Step 6 on their comparison bits → a theorem that the simulators' comparison bits on two edge queries satisfy the condition; reason: the source uses this implicitly; it is the property that puts Step 6 in the constrained case
--   - reading: Steps 4–5 are executed after Step 3 (where a simulator with a non-edge query aborts) → hypotheses that both queries are edges; reason: the claim concerns the bits computed by two simulators that have not aborted
--   - encoding: an identity between the bits the simulators compute → the identity on every outcome of positive probability (the support of the output law); reason: an identity of random bits holds surely; for a discrete law this is exactly the support
--   - encoding: a graph G on the labels 0, …, |V|−1, with query bits in F₂ → G : SimpleGraph (Fin n) with decidable adjacency, Query n := Fin n × Fin n × Bool; reason: Fin n is the source label set and Bool is its two-element query alphabet; finite adjacency admits a decision procedure
--   - encoding: (i, j) ∈ E, edges always represented with i < j → IsValid G (i, j, r) := i < j ∧ G.Adj i j; reason: the source's own convention for membership of an ordered pair in E (p.9)
--   - encoding: each vertex label written as an h-bit string, h = ⌈log₂|V|⌉, with k-th bit i_k → h = Nat.clog 2 n and i_k = Nat.testBit i (k − 1) (least significant bit first); reason: the source fixes no bit order; any injective h-bit encoding of the labels is the source's construction
--   - encoding: u, v ∈ {0,1}, complemented indices, and products of comparison bits → Bool indices, Boolean negation !, xor, and && in ValidPattern; reason: these are the same two-element alphabets and bit products as in Fig. 10
-- source:
--   Claude Crépeau, Harmanpreet Singh Grover, April Niu, Nan Yang, Fadi Younes, Relativistic Zero Knowledge, STOC 2027 submission #205 (October 2026), p.11, Fig. 10 (condition on the inputs), used in Step 6, p.10

import Mathlib
import Definitions.Def_RelativisticZK205_ThreeCol_Simulator

namespace RelativisticZK205.ThreeCol

/-- Fig. 10, p.11: when neither simulator aborts, the bits `m_uv = z_uv ⊕ z'_uv` produced by
preprocessing satisfy the condition that each vertex matches at most one vertex on the other side,
`∀ u v, m_uv · m_uv̄ = m_uv · m_ūv = 0`, on every outcome of positive probability. -/
theorem query_pattern_valid {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (i j i' j' : Fin n) (r r' : Bool) (h₁ : IsValid G (i, j, r)) (h₂ : IsValid G (i', j', r')) :
    ∀ p ∈ (preprocess G (i, j, r) (i', j', r')).support,
      ValidPattern fun u v => xor (p.1.2 u v) (p.2.2 u v) := by sorry

end RelativisticZK205.ThreeCol
