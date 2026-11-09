-- Prove2me | Theorems.Thm_RelativisticZK205_ThreeCol_response_channels_identical
-- name    : RelativisticZK205.ThreeCol.response_channels_identical
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:17:36.654914+00:00
-- url     : https://prove2.me/theorems/7f182be2-9a1f-4711-8225-052bbaf322a6
-- title:
--   Proof of Theorem 1 (p.11) — the real and simulated response laws are identical for all verifier messages
-- statement:
--   Let $c$ be a proper 3-colouring of $G$. For every pair of verifier messages $q_1,q_2$, the simulators' joint replies and the real provers' joint replies have the same law:
--
--   $$
--   \mathrm{Sim}_G(q_1,q_2)=\mathrm{Real}_{G,c}(q_1,q_2).
--   $$
--
--   The simulated channel does not depend on $c$. Since verifiers interact with the provers only through this channel, any verifiers, including those whose messages depend on auxiliary inputs, see the same thing in both worlds.
--
--   Differences from the source:
--   - encoding: a graph G = (V, E) whose vertices are labelled by distinct integers 0, …, |V|−1, with a 3-colouring C = {(i, c_i)}, c_i ∈ F₃, (i, j) ∈ E ⇒ c_j ≠ c_i → G : SimpleGraph (Fin n) with decidable adjacency, c : Fin n → ZMod 3 with G.Adj x y → c x ≠ c y; bits of F₂ are Bool; reason: the same graphs and colourings; Fin n is the label set {0, …, n−1}
--   - encoding: (i, j) ∈ E, edges always represented with i < j → IsValid G (i, j, r) := i < j ∧ G.Adj i j; reason: the source's own convention for membership of an ordered pair in E (p.9)
--   - encoding: an aborting simulator S_i stops (Step 3) and the honest prover aborts → an abort is the reply none; an aborting simulator still takes part in every box instance of the fixed wiring with constant inputs (false, or the all-false table and r = false) and replies none; reason: the boxes are No-Signalling, so the other party's outputs have the same law whatever the aborting party inputs; the wiring has a fixed common order (pp.4–5)
--   - encoding: each vertex label written as an h-bit string, h = ⌈log₂|V|⌉, with k-th bit i_k → h = Nat.clog 2 n and i_k = Nat.testBit i (k − 1) (least significant bit first); reason: the source fixes no bit order; any injective h-bit encoding of the labels is the source's construction
-- source:
--   Claude Crépeau, Harmanpreet Singh Grover, April Niu, Nan Yang, Fadi Younes, Relativistic Zero Knowledge, STOC 2027 submission #205 (October 2026), p.11, proof of Theorem 1 ("Thus, the real and simulated joint output distributions are identical for arbitrary verifier messages …")

import Mathlib
import Definitions.Def_RelativisticZK205_ThreeCol_Simulator

namespace RelativisticZK205.ThreeCol

/-- Proof of Theorem 1, p.11: for a proper 3-colouring `c`, the simulators' joint replies have
the same law as the real provers' joint replies, for every pair of verifier messages. -/
theorem response_channels_identical {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n → ZMod 3) (hc : ∀ x y, G.Adj x y → c x ≠ c y) :
    ∀ q₁ q₂ : Query n, simChannel G q₁ q₂ = realChannel G c q₁ q₂ := by sorry

end RelativisticZK205.ThreeCol
