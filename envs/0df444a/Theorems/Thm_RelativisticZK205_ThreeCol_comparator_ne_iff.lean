-- Prove2me | Theorems.Thm_RelativisticZK205_ThreeCol_comparator_ne_iff
-- name    : RelativisticZK205.ThreeCol.comparator_ne_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:17:57.629552+00:00
-- url     : https://prove2.me/theorems/ebc6eebc-187f-4621-b988-7ac5d2773cf8
-- title:
--   Step 4 — $z_{00}\neq z'_{00}$ if and only if $i=i'$
-- statement:
--   Let $G$ be a graph on $n$ vertices and let the simulators receive edge queries $((i,j),r)$ and $((i',j'),r')$, so that neither aborts. After preprocessing, on every outcome of the PR-boxes, the comparison bits $z_{00}$ of $S_1$ and $z'_{00}$ of $S_2$ satisfy
--
--   $$
--   z_{00}\neq z'_{00}\iff i=i'.
--   $$
--
--   Thus two simulators that cannot communicate learn, in XOR-shared form, whether their first vertices coincide. Combined with Step 5 it gives the four comparison bits fed to 3-COLZK.
--
--   Differences from the source:
--   - reading: Steps 4–5 are executed after Step 3 (where a simulator with a non-edge query aborts) → hypotheses that both queries are edges; reason: the claim concerns the bits computed by two simulators that have not aborted
--   - encoding: each vertex label written as an h-bit string, h = ⌈log₂|V|⌉, with k-th bit i_k → h = Nat.clog 2 n and i_k = Nat.testBit i (k − 1) (least significant bit first); reason: the source fixes no bit order; any injective h-bit encoding of the labels is the source's construction
--   - encoding: an identity between the bits the simulators compute → the identity on every outcome of positive probability (the support of the output law); reason: an identity of random bits holds surely; for a discrete law this is exactly the support
--   - encoding: a graph G on the labels 0, …, |V|−1, with query bits in F₂ → G : SimpleGraph (Fin n) with decidable adjacency, Query n := Fin n × Fin n × Bool; reason: Fin n is the source label set and Bool is its two-element query alphabet; finite adjacency admits a decision procedure
--   - encoding: (i, j) ∈ E, edges always represented with i < j → IsValid G (i, j, r) := i < j ∧ G.Adj i j; reason: the source's own convention for membership of an ordered pair in E (p.9)
-- source:
--   Claude Crépeau, Harmanpreet Singh Grover, April Niu, Nan Yang, Fadi Younes, Relativistic Zero Knowledge, STOC 2027 submission #205 (October 2026), p.10, Step 4; p.11, first display of the proof of Theorem 1

import Mathlib
import Definitions.Def_RelativisticZK205_ThreeCol_Simulator

namespace RelativisticZK205.ThreeCol

/-- Step 4, p.10 (and the first display of the proof of Theorem 1, p.11): when neither simulator
aborts, i.e. both queries `((i, j), r)` and `((i', j'), r')` are edges, the bits `z₀₀` of `S₁` and
`z'₀₀` of `S₂` computed in preprocessing differ if and only if `i = i'`, on every outcome of
positive probability. -/
theorem comparator_ne_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (i j i' j' : Fin n) (r r' : Bool) (h₁ : IsValid G (i, j, r)) (h₂ : IsValid G (i', j', r')) :
    ∀ p ∈ (preprocess G (i, j, r) (i', j', r')).support,
      (p.1.2 false false ≠ p.2.2 false false ↔ i = i') := by sorry

end RelativisticZK205.ThreeCol
