-- Prove2me | Theorems.Thm_SubcubicBA_PlainPKI_lemma_10
-- name    : SubcubicBA.PlainPKI.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:45:53.335389+00:00
-- url     : https://prove2.me/theorems/92a59b1f-1295-4d38-b9cd-c0f4dd735400
-- title:
--   Lemma 10 — committee broadcast
-- statement:
--   Run CommitteeBroadcast with sender $p_{in}\in C$ and committee $C\subseteq\{0,\dots,n-1\}$, against a rushing Dolev–Yao adversary with any admissible auxiliary knowledge and any set $F$ of byzantine parties, with any ordering of simultaneous arrivals. If at least one member of $C$ is honest, the protocol satisfies byzantine broadcast:
--   1. every honest party outputs a value or $\bot$ by round $2|C|+1$;
--   2. any two honest outputs are equal; and
--   3. if $p_{in}$ is honest, every honest party outputs $p_{in}$'s input.
--
--   Agreement thus needs only one honest committee member, which is what makes batching broadcasts through a small committee possible.
--
--   Differences from the source:
--   - reading: byzantine broadcast (used, never defined) → termination by round 2|C| + 1, agreement of all honest outputs (⊥ allowed), validity for an honest sender; reason: the standard definition, which the proof of Lemma 10 checks (paper.md item 8)
--   - reading: "a message signed by p_in and i − 1 parties from C", processed in an iteration of two rounds → valid signatures of p_in and of at least i − 1 distinct members of C (p_in counted); every party accepts and forwards to C in round 2i − 3, members of C accept and sign in round 2i − 2; reason: at i = 2 the sender's chain must be accepted, and the relay of the proof of Lemma 10 needs this round structure
--   - encoding: "only applied for two distinct messages received" → forwarding and signing only for the first two distinct accepted values, simultaneous arrivals ordered by an arbitrary key; reason: the arbitrary order quantified universally
--   - generalization: n parties of which at most t < n/2 are byzantine (§5) → any set of byzantine parties, provided one member of C is honest; reason: the proof of Lemma 10 does not use t < n/2
--   - generalization: a protocol run on its own → the guarantee holds against every admissible auxiliary adversary knowledge (anything without honest signatures of the instance's session subtree); reason: makes the specifications composable; the source's standalone run is the case aux = ∅
--   - reading: computationally unforgeable κ-bit signatures and a collision-resistant κ-bit hash (§4, p. 8) → idealized symbolic tokens: injective constructors sig p m, hash m; Dolev–Yao adversary; honest parties see tokens only through blinded shapes, equality tests and signature verification (with unbounded local computation they can recognise a token whose content they could construct themselves, but never obtain a signature they have not received); reason: every proof in the paper uses unforgeability and collision resistance as absolute facts (pp. 12, 16, 30) and no reduction appears (paper.md reading 1)
--   - generalization: a static adversary; rushing is not specified → a static rushing adversary: its round-r messages may depend on the honest round-r messages sent to corrupted parties; reason: a stronger adversary; every execution against a non-rushing adversary is one of these
--   - generalization: byzantine parties cannot forge signatures or invert the hash → the adversary may also open signature and hash tokens it holds (it still cannot create an honest party's signature); reason: a stronger adversary; the source's adversary is a special case
--   - encoding: messages of a given bit size; signatures and hashes of κ bits → symbolic terms of bit size: 2-bit tag per data node, a self-delimiting code for numbers, exactly κ bits per token; reason: the sizes of §4; constant per-node overheads do not change any instance's asymptotics
--   - encoding: instance tags on messages and signatures (§13) → every signature is domain-separated by the session number of its protocol instance; sub-instances get child sessions; reason: the §13 tags; replay across instances is excluded exactly as §13 intends
-- source:
--   Marc Dufay, Roger Wattenhofer, Optimal Subcubic Byzantine Agreement with Plain PKI, STOC 2027 submission #101 (October 2026), Lemma 10, p. 23 (CommitteeBroadcast, pp. 22–23)

import Mathlib
import Definitions.Def_SubcubicBA_PlainPKI_Model
import Definitions.Def_SubcubicBA_PlainPKI_Proofs
import Definitions.Def_SubcubicBA_PlainPKI_CommitteeBroadcast

namespace SubcubicBA.PlainPKI

/-- Lemma 10 (p. 23). -/
theorem lemma_10 (pin : ℕ) (C : Finset ℕ) (ordKey : ℕ → ℕ → ℕ → ℕ → ℕ)
    (n sess t κ : ℕ) (inp : Fin n → Term) (F : Finset (Fin n)) (aux : Set Term) (tr : Trace n)
    (hpin : pin ∈ C) (hC : ∀ q ∈ C, q < n) (hhonest : ∃ q : Fin n, q.val ∈ C ∧ q ∉ F)
    (hfresh : FreshAux (⟨sess, t, κ, inp, F⟩ : Setup n) aux)
    (hrun : IsRun (committeeBroadcast pin C ordKey) ⟨sess, t, κ, inp, F⟩ aux tr) :
    (∀ j : Fin n, j ∉ F → ∃ r ≤ 2 * C.card + 1, ∃ m : Option Term,
        OutputsAt (committeeBroadcast pin C ordKey) ⟨sess, t, κ, inp, F⟩ tr j r (Term.opt m)) ∧
    (∀ j k : Fin n, j ∉ F → k ∉ F → ∀ o o' : Term,
        Outputs (committeeBroadcast pin C ordKey) ⟨sess, t, κ, inp, F⟩ tr j o →
        Outputs (committeeBroadcast pin C ordKey) ⟨sess, t, κ, inp, F⟩ tr k o' → o = o') ∧
    (∀ hp : pin < n, (⟨pin, hp⟩ : Fin n) ∉ F → ∀ j : Fin n, j ∉ F → ∀ o : Term,
        Outputs (committeeBroadcast pin C ordKey) ⟨sess, t, κ, inp, F⟩ tr j o →
          o = Term.opt (some (inp ⟨pin, hp⟩))) := by sorry

end SubcubicBA.PlainPKI
