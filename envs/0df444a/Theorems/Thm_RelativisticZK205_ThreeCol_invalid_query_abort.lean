-- Prove2me | Theorems.Thm_RelativisticZK205_ThreeCol_invalid_query_abort
-- name    : RelativisticZK205.ThreeCol.invalid_query_abort
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:17:50.828859+00:00
-- url     : https://prove2.me/theorems/4da7dec3-37be-40a0-b239-7ddb3698ca63
-- title:
--   Proof of Theorem 1 (p.11) — on an invalid query the simulators reproduce the abort behaviour
-- statement:
--   Let $c$ be any colouring and let $q_1,q_2$ be queries at least one of which is not an edge. Then the simulators' joint replies have exactly the law of the real provers' joint replies:
--
--   $$
--   \mathrm{Sim}_G(q_1,q_2)=\mathrm{Real}_{G,c}(q_1,q_2).
--   $$
--
--   The side with an invalid query aborts in both worlds, and a side with a valid query answers with a uniform pair in $\mathbb Z_3^2$ in both worlds.
--
--   Differences from the source:
--   - generalization: a proper 3-colouring C of G → an arbitrary map c : Fin n → ZMod 3; reason: this case uses no property of the colouring; proper colourings are a special case
--   - reading: each S_i reproduces the honest prover's local abort behaviour → equality of the simulated and real joint reply laws whenever at least one query is not an edge; reason: this is the case of the final equality of the proof that the sentence settles
--   - encoding: a graph G on the labels 0, …, |V|−1, and values c_i ∈ F₃; query bits in F₂ → G : SimpleGraph (Fin n) with decidable adjacency, c : Fin n → ZMod 3, and Bool query bits; properness is not assumed; reason: the graph, label and field representations are unchanged; dropping properness is the separate declared generalization
--   - encoding: (i, j) ∈ E, edges always represented with i < j → IsValid G (i, j, r) := i < j ∧ G.Adj i j; reason: the source's own convention for membership of an ordered pair in E (p.9)
--   - encoding: an aborting simulator S_i stops (Step 3) and the honest prover aborts → an abort is the reply none; an aborting simulator still takes part in every box instance of the fixed wiring with constant inputs (false, or the all-false table and r = false) and replies none; reason: the boxes are No-Signalling, so the other party's outputs have the same law whatever the aborting party inputs; the wiring has a fixed common order (pp.4–5)
--   - encoding: each vertex label written as an h-bit string, h = ⌈log₂|V|⌉, with k-th bit i_k → h = Nat.clog 2 n and i_k = Nat.testBit i (k − 1) (least significant bit first); reason: the source fixes no bit order; any injective h-bit encoding of the labels is the source's construction
-- source:
--   Claude Crépeau, Harmanpreet Singh Grover, April Niu, Nan Yang, Fadi Younes, Relativistic Zero Knowledge, STOC 2027 submission #205 (October 2026), p.11, proof of Theorem 1 ("On an invalid query, each S_i will reproduce the honest prover's local abort behaviour.")

import Mathlib
import Definitions.Def_RelativisticZK205_ThreeCol_Simulator

namespace RelativisticZK205.ThreeCol

/-- Proof of Theorem 1, p.11: if at least one of the two queries is not an edge, the simulators'
joint replies have the same law as the real provers' (the aborting side replies `none`, and a
non-aborting side's reply is distributed as in the real protocol). -/
theorem invalid_query_abort {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n → ZMod 3) (q₁ q₂ : Query n) (h : ¬ IsValid G q₁ ∨ ¬ IsValid G q₂) :
    simChannel G q₁ q₂ = realChannel G c q₁ q₂ := by sorry

end RelativisticZK205.ThreeCol
