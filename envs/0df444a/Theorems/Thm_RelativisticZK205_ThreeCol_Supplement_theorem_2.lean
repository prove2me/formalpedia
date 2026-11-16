-- Prove2me | Theorems.Thm_RelativisticZK205_ThreeCol_Supplement_theorem_2
-- name    : RelativisticZK205.ThreeCol.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:32:28.608801+00:00
-- url     : https://prove2.me/theorems/89de8f9f-a025-4f33-bcea-e3b32f1a454b
-- title:
--   Theorem 2 — exact No-Signalling simulation of Γ_LHV
-- statement:
--   Let $G$ be any finite simple graph on $n$ vertices, $C$ any fixed Hamiltonian-cycle witness of $G$, and $k\in\mathbb N$. Put $\ell=\lceil\log_2(64n!2^{3k})\rceil$. Let $F$ be any field of cardinality $2^\ell$ with a chosen $\mathbb F_2$ coordinate basis $e$. Write $R_{G,C}$ for the honest Γ_LHV field strategy and $S_{G,e}$ for the explicit simulator using the published PR-box. The simulator receives no $C$.
--
--   It reserves exactly $n^2\ell$ PR instances, its response channel is No-Signalling, and for every matrix query $X$ and challenge $c$, including either local malformed-query branch,
--   $$\operatorname{Law}(R_{G,C}(X,c))=\operatorname{Law}(S_{G,e}(X,c)).$$
--   Both orders of interface invocation give this same joint response law. The distribution already delivered to either first caller equals the corresponding marginal of that law, without waiting for the other input.
--
--   For every pair of bounded local stochastic verifier programs $M_A,M_B$, every finite bank $R$ of independently initialized No-Signalling verifier resources, all auxiliary strings $a_A,a_B$, every independent shared/private initial verifier coin law $\mu$, and every finite interleaving $\sigma$,
--   $$\operatorname{Experiment}(R_{G,C},R,M_A,M_B,\mu,\sigma)
--   =\operatorname{Experiment}(S_{G,e},R,M_A,M_B,\mu,\sigma).$$
--   These are full joint distributions of the two final verifier states and outputs. In particular both transcripts, retained private randomness and memory may be included. Bob's challenge may depend on his local history through a No-Signalling resource accessed after Alice has received the commitment. Neither honest uniform queries, advance selection of the challenge, nor acceptance-only comparisons are imposed.
--
--   This companion theorem establishes perfect simulation of the Hamiltonian-cycle protocol; it is independent of the mission’s published 3-coloring goal. No statistical error allowance or complexity corollary replaces the equality.
--
--   Differences from the source:
--   - encoding: finite graph, Hamiltonian cycle and lexicographic cycle unveiling → Fin n vertices and canonical undirected cycle edge sets, with restricted finite mask functions and sorted serialization; reason: retains every simple Hamiltonian cycle while identifying rotations and reversal and transmitting only opened masks
--   - encoding: F_(2^ell) and binary field coordinates → an arbitrary finite field with an additive equivalence to (ZMod 2)^ell; ell = Nat.clog 2 (64 * n! * 2^(3*k)); reason: this is precisely an F₂ basis; the real device still computes actual field arithmetic, so no field size or source instance is lost
--   - encoding: each simulator reproduces its honest prover’s local abort on an invalid query → Option input/reply alphabets with independent local abort branches; reason: all malformed encodings have the same protocol response; the verifier may retain their raw bytes in its private state
--   - encoding: local black-box access to initialized No-Signalling resources and arbitrary verifier outputs → bounded local stochastic programs, independent resource instances, both first-interface marginals and conditional second interfaces, every finite interleaving, and the full final verifier state law; reason: makes the paper’s p.5 causal wiring semantics explicit, including challenges chosen after Alice’s reply; transcripts and coins may be retained as local memory
--   - generalization: the polynomial-time verifiers of Definition 22 and Theorem 2’s exact joint-output assertion → all bounded finite-state stochastic verifiers without a computational restriction, equality in both response orders and of prefix laws, and the exact n²ell reserved PR count; reason: each source verifier on fixed bounded inputs is such a program; the proof is information-theoretic and pp.12–13 provide the pointwise laws, delayed interfaces and count
-- source:
--   Claude Crépeau, Harmanpreet Singh Grover, April Niu, Nan Yang, Fadi Younes, Relativistic Zero Knowledge, STOC 2027 submission #205 (October 2026), p.13, Theorem 2; pp.12–13, Protocol Γ_LHV and its explicit simulators; pp.5, 8–9, local wirings and Definitions 18–22

import Mathlib
import Definitions.Def_RelativisticZK205_ThreeCol_Supplement_Field

namespace RelativisticZK205.ThreeCol.Supplement

/-- Theorem 2, p.13, with the named simulators evaluated through their actual
local PR interfaces. The statement includes both response orders and all prefix
laws, and arbitrary finite local stochastic verifiers using independent
No-Signalling resources in any bounded interleaving. Neither simulation equality
nor a witness-independent real distribution is a hypothesis. -/
theorem theorem_2 {n : ℕ} (G : SimpleGraph (Vertex n)) (C : EdgeSet n)
    (hC : IsWitness G C) (k : ℕ)
    {F : Type} [Field F] [Fintype F] (e : Coordinates F (bitLength n k)) :
    let ℓ := bitLength n k
    let real := realFieldDevice (F := F) G C
    let sim := simFieldDevice G e
    reservedPR n ℓ = n ^ 2 * ℓ ∧
    IsNoSignalling sim.joint ∧
    (∀ (X : Option (FieldMatrix F n)) (c : BobQuery),
      real.joint X c = sim.joint X c ∧
      real.reverseJoint X c = real.joint X c ∧
      sim.reverseJoint X c = sim.joint X c ∧
      real.alicePrefix X = (real.joint X c).map Prod.fst ∧
      sim.alicePrefix X = (sim.joint X c).map Prod.fst ∧
      real.bobPrefix c = (real.joint X c).map Prod.snd ∧
      sim.bobPrefix c = (sim.joint X c).map Prod.snd) ∧
    (∀ (I J U V SA SB OA OB Coins : Type)
      [Fintype I] [Fintype J] [Fintype U] [Fintype V]
      [Inhabited I] [Inhabited J] [Inhabited U] [Inhabited V]
      [Fintype SA] [Fintype SB] [Fintype OA] [Fintype OB] [Fintype Coins]
      (m : ℕ) (R : Fin m → Channel I J U V),
      (∀ i, IsNoSignalling (R i)) →
      ∀ (MA : LocalMachine (Option (FieldMatrix F n)) (Option (FieldMatrix F n)) I U SA OA)
        (MB : LocalMachine BobQuery (Option (FieldOpening F n)) J V SB OB)
        (coins : PMF Coins) (initA : List Bool → Coins → SA) (initB : List Bool → Coins → SB)
        (auxA auxB : List Bool) (schedule : List Bool),
      let init := coins.map (fun r => (initA auxA r, initB auxB r))
      experiment real m R MA MB init schedule = experiment sim m R MA MB init schedule) := by sorry

end RelativisticZK205.ThreeCol.Supplement
