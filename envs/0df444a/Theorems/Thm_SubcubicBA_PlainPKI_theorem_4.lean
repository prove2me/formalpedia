-- Prove2me | Theorems.Thm_SubcubicBA_PlainPKI_theorem_4
-- name    : SubcubicBA.PlainPKI.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:46:12.452534+00:00
-- url     : https://prove2.me/theorems/a25b8b8f-530b-4484-9828-af5220b88f0b
-- title:
--   Theorem 4 — ProofCreation gives n/10 honest parties a proof (corrected: Votes include first-round votes)
-- statement:
--   Run ProofCreation (as defined round by round in the definition `ProofCreation`) with binary inputs on $n$ parties, at most $t<n/2$ of them byzantine, against a rushing Dolev–Yao adversary with any admissible auxiliary knowledge, and with any resolution of the paper's arbitrary choices. Suppose
--   1. $G_1$ is an $(n/20,\,7n/10)$-disperser for every $n$, and
--   2. $G_2$ is fault-tolerant: for every $C$ with $2|C|<n$ there is $S$ disjoint from $C$ with $|S|\ge4n/10$, $G_2[S]$ connected and any two vertices of $S$ at distance at most $\rho(n)$ in $G_2[S]$, where $\rho(n)$ is the number of SpreadVotes rounds.
--
--   Then
--   $$\#\{\text{honest }j:\ j\text{ outputs a proof (Definition 10) for }0\text{ or }1\}\ge\frac n{10}.$$
--
--   This is the partial-decision property of proof creation, the first half of the weak agreement protocol.
--
--   Differences from the source:
--   - correction: ProofCreation with Votes = the votes received in the second round only (pseudocode, p. 13) → Votes = the valid votes received in both voting rounds, used by SpreadVotes and ComputeProof; reason: counterexample to the printed protocol: n = 5, t = 2, honest 0, 1, 2 with inputs 0, 0, 1, byzantine 3, 4 send round-0 votes 0 to parties 0, 1 and 1 to party 2 (so no honest party switches to ⊥) and stay silent afterwards; then |A| = 3 > 3n/10 disables CakeLeader, no party has t + 1 second-round votes for b or ⊥, and every honest party outputs ⊥; the proof (case nb⊥ ≤ 4n/10) uses the first-round votes, and "all votes received are preserved" (p. 13)
--   - generalization: G₁ from Theorem 11 (α = 1/20) and G₂ from Theorem 2, with O(log n) SpreadVotes rounds → any families with the (n/20, 7n/10)-disperser property and the fault-tolerance property for |C| < n/2 with |S| ≥ 4n/10 and diameter ≤ ρ(n), where ρ(n) is the SpreadVotes length; reason: the proof uses only these properties; Theorem 2 (α = 1/2, β ≤ 6/5) and Theorem 11 supply them
--   - reading: (SPLIT, l, m, ⌈|A|/2⌉) in CakeLeader → (SPLIT, l, r, ⌈|A|/2⌉); reason: m is not yet defined at that line; the helper's query is (l, r, i)
--   - encoding: "breaking ties arbitrarily", "there exists p_j", "a maximum matching", "a set of t + 1 votes/accusations" → every choice, through the universally quantified PCChoice; reason: the arbitrary choices of the pseudocode quantified universally
--   - encoding: the recursive pseudocode with "wait two rounds" → a lock-step schedule: level d queries in round 3 + 2d, answers in round 4 + 2d, ⌈log₂ n⌉ + 1 levels; reason: a synchronous realization of the pseudocode
--   - generalization: a protocol run on its own → the guarantee holds against every admissible auxiliary adversary knowledge (anything without honest signatures of the instance's session subtree); reason: makes the specifications composable; the source's standalone run is the case aux = ∅
--   - reading: computationally unforgeable κ-bit signatures and a collision-resistant κ-bit hash (§4, p. 8) → idealized symbolic tokens: injective constructors sig p m, hash m; Dolev–Yao adversary; honest parties see tokens only through blinded shapes, equality tests and signature verification (with unbounded local computation they can recognise a token whose content they could construct themselves, but never obtain a signature they have not received); reason: every proof in the paper uses unforgeability and collision resistance as absolute facts (pp. 12, 16, 30) and no reduction appears (paper.md reading 1)
--   - generalization: a static adversary; rushing is not specified → a static rushing adversary: its round-r messages may depend on the honest round-r messages sent to corrupted parties; reason: a stronger adversary; every execution against a non-rushing adversary is one of these
--   - generalization: byzantine parties cannot forge signatures or invert the hash → the adversary may also open signature and hash tokens it holds (it still cannot create an honest party's signature); reason: a stronger adversary; the source's adversary is a special case
--   - encoding: messages of a given bit size; signatures and hashes of κ bits → symbolic terms of bit size: 2-bit tag per data node, a self-delimiting code for numbers, exactly κ bits per token; reason: the sizes of §4; constant per-node overheads do not change any instance's asymptotics
--   - encoding: instance tags on messages and signatures (§13) → every signature is domain-separated by the session number of its protocol instance; sub-instances get child sessions; reason: the §13 tags; replay across instances is excluded exactly as §13 intends
-- source:
--   Marc Dufay, Roger Wattenhofer, Optimal Subcubic Byzantine Agreement with Plain PKI, STOC 2027 submission #101 (October 2026), Theorem 4, p. 20 (ProofCreation and subprotocols, pp. 13–19)

import Mathlib
import Definitions.Def_SubcubicBA_PlainPKI_Model
import Definitions.Def_SubcubicBA_PlainPKI_Graphs
import Definitions.Def_SubcubicBA_PlainPKI_Proofs
import Definitions.Def_SubcubicBA_PlainPKI_CommitteeBroadcast
import Definitions.Def_SubcubicBA_PlainPKI_ProofCreation

namespace SubcubicBA.PlainPKI

open Classical in
/-- Theorem 4 (p. 20). -/
theorem theorem_4 (G₁ : (n : ℕ) → Fin n → Finset (Fin n)) (G₂ : (n : ℕ) → SimpleGraph (Fin n))
    (ρ : ℕ → ℕ) (ch : PCChoice)
    (hG₁ : ∀ n : ℕ, IsDisperser (G₁ n) ((n : ℝ) / 20) (7 * (n : ℝ) / 10))
    (hG₂ : ∀ n : ℕ, ∀ C : Finset (Fin n), 2 * C.card < n →
      ∃ S : Finset (Fin n), Disjoint S C ∧ 4 * (n : ℝ) / 10 ≤ (S.card : ℝ) ∧
        ((G₂ n).induce (S : Set (Fin n))).Connected ∧
        ∀ u v : (S : Set (Fin n)), ((G₂ n).induce (S : Set (Fin n))).dist u v ≤ ρ n)
    (n sess t κ : ℕ) (b : Fin n → Bool) (F : Finset (Fin n)) (aux : Set Term) (tr : Trace n)
    (ht : 2 * t < n) (hF : F.card ≤ t) (hfresh : FreshAux (baSetup sess t κ b F) aux)
    (hrun : IsRun (proofCreation G₁ G₂ ρ ch) (baSetup sess t κ b F) aux tr) :
    (n : ℝ) ≤ 10 * ((Finset.univ.filter fun j : Fin n => j ∉ F ∧ ∃ m : Term,
        (∃ c ≤ 1, IsProofTerm sess n t c m) ∧
        Outputs (proofCreation G₁ G₂ ρ ch) (baSetup sess t κ b F) tr j (Term.opt (some m))).card : ℝ) := by sorry

end SubcubicBA.PlainPKI
