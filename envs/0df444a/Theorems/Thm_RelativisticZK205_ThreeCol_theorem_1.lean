-- Prove2me | Theorems.Thm_RelativisticZK205_ThreeCol_theorem_1
-- name    : RelativisticZK205.ThreeCol.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:20:30.646705+00:00
-- url     : https://prove2.me/theorems/15f0fa9a-eae0-4c8e-91ca-065772707454
-- title:
--   Theorem 1 — No-Signalling simulators reproduce exactly the verifiers' joint output distribution in $\Pi^{(2)}_{\mathrm{LHV}}$
-- statement:
--   Let $G$ be a graph on $n$ vertices and $c$ a proper 3-colouring of $G$. Let $\mathrm{Real}_{G,c}$ be the real provers' joint response channel in protocol $\Pi^{(2)}_{\mathrm{LHV}}[G,c]$, and $\mathrm{Sim}_G$ the joint response channel of the simulators $(S_1,S_2)$ of §5.1, a local wiring of PR-boxes and one 3-COLZK channel that uses $G$ but not $c$. Then:
--
--   1. the PR-box, the 3-COLZK channel and the simulators' channel $\mathrm{Sim}_G$ are No-Signalling;
--   2. for all verifier messages $q_1,q_2$, $\ \mathrm{Sim}_G(q_1,q_2)=\mathrm{Real}_{G,c}(q_1,q_2)$;
--   3. for every one-round verifier pair $V$ (arbitrary auxiliary-input, memory and output types) and all auxiliary inputs $a_1,a_2$,
--
--   $$
--   \mathrm{run}(V,\mathrm{Sim}_G,a_1,a_2)=\mathrm{run}(V,\mathrm{Real}_{G,c},a_1,a_2).
--   $$
--
--   So the simulators, which never see the colouring and cannot signal, produce exactly the same joint output distribution as the same verifiers interacting with the real provers. This is the perfect zero-knowledge property of the [ABC+21] 3-colouring protocol against No-Signalling verifiers, with No-Signalling simulators.
--
--   Differences from the source:
--   - generalization: for any No-Signalling verifiers (polynomial-time in Definition 22) → for every verifier pair given as a two-stage kernel (ask, finish), with arbitrary auxiliary-input, memory and output types; neither No-Signalling nor polynomial time is assumed; reason: the conclusion holds for every such kernel; No-Signalling polynomial-time verifiers are a special case
--   - reading: the joint output distribution of the same verifiers in Π^(2)_LHV, in a model whose multi-round strategies are deferred to a forthcoming paper (§2.4) → the one-round run (both queries picked, then the replies, then the outputs), together with clause 2, equality of the two response channels for every pair of messages; reason: §2.4 defines only single-round channels; a verifier pair that interleaves (V′₂ picking q₂ after V′₁ receives w₁, through a No-Signalling V̂′) sees the provers only through the response channel, so clause 2 with clause 1 settles it
--   - reading: the No-Signalling simulators above (polynomial-time ITMs, Definitions 21–22) → the explicit local wiring simWiring G over {PR, 3-COLZK}, with clause 1 stating that PR, 3-COLZK and the simulated channel are No-Signalling; no running-time bound is stated; reason: Theorem 1 states exact equality for the specified simulators; this item formalizes that output-law claim, while channel_count separately records the number of box instances. Turing-machine running-time and spacetime guarantees belong to the surrounding class-level claim, outside this mission
--   - encoding: a graph G = (V, E) whose vertices are labelled by distinct integers 0, …, |V|−1, with a 3-colouring C = {(i, c_i)}, c_i ∈ F₃, (i, j) ∈ E ⇒ c_j ≠ c_i → G : SimpleGraph (Fin n) with decidable adjacency, c : Fin n → ZMod 3 with G.Adj x y → c x ≠ c y; bits of F₂ are Bool; reason: the same graphs and colourings; Fin n is the label set {0, …, n−1}
--   - encoding: (i, j) ∈ E, edges always represented with i < j → IsValid G (i, j, r) := i < j ∧ G.Adj i j; reason: the source's own convention for membership of an ordered pair in E (p.9)
--   - encoding: an aborting simulator S_i stops (Step 3) and the honest prover aborts → an abort is the reply none; an aborting simulator still takes part in every box instance of the fixed wiring with constant inputs (false, or the all-false table and r = false) and replies none; reason: the boxes are No-Signalling, so the other party's outputs have the same law whatever the aborting party inputs; the wiring has a fixed common order (pp.4–5)
--   - encoding: each vertex label written as an h-bit string, h = ⌈log₂|V|⌉, with k-th bit i_k → h = Nat.clog 2 n and i_k = Nat.testBit i (k − 1) (least significant bit first); reason: the source fixes no bit order; any injective h-bit encoding of the labels is the source's construction
-- source:
--   Claude Crépeau, Harmanpreet Singh Grover, April Niu, Nan Yang, Fadi Younes, Relativistic Zero Knowledge, STOC 2027 submission #205 (October 2026), p.11, Theorem 1 (simulator p.10, protocol pp.9–10)

import Mathlib
import Definitions.Def_RelativisticZK205_ThreeCol_Simulator
import Definitions.Def_RelativisticZK205_ThreeCol_Verifier

namespace RelativisticZK205.ThreeCol

/-- Theorem 1, p.11. For every graph `G` on `Fin n` and every proper 3-colouring `c` of `G`:
1. the boxes used by the simulators, PR and 3-COLZK, are No-Signalling, and so is the simulators'
   joint response channel `simChannel G` (which does not depend on `c`);
2. the simulators' joint replies have exactly the law of the real provers' joint replies in
   `Π^(2)_LHV[G, c]`, for every pair of verifier messages;
3. hence, for every one-round verifier pair `V` (with any auxiliary-input, memory and output types)
   and all auxiliary inputs `a₁, a₂`, the joint output distribution with the simulators equals the
   joint output distribution with the real provers. -/
theorem theorem_1 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n → ZMod 3) (hc : ∀ x y, G.Adj x y → c x ≠ c y) :
    IsNoSignalling prBox ∧ IsNoSignalling threeColZK ∧ IsNoSignalling (simChannel G) ∧
    (∀ q₁ q₂ : Query n, simChannel G q₁ q₂ = realChannel G c q₁ q₂) ∧
    ∀ (Aux State O : Type) (V : Verifier Aux State (Query n) Reply O) (a₁ a₂ : Aux),
      V.run (simChannel G) a₁ a₂ = V.run (realChannel G c) a₁ a₂ := by sorry

end RelativisticZK205.ThreeCol
