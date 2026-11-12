-- Prove2me | Theorems.Thm_SubcubicBA_PlainPKI_theorem_3
-- name    : SubcubicBA.PlainPKI.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:44:55.585221+00:00
-- url     : https://prove2.me/theorems/0f500e95-3fbc-4cd2-8929-439c9a0c5604
-- title:
--   Theorem 3 — WeakBA is a weak agreement protocol
-- statement:
--   Let PC be any proof-creation protocol satisfying Definition 8 with round bound $T_1$ and whose proofs are sound (Definition 5: when all honest inputs are $1-v$, no proof for $v$ is derivable by the adversary from what has been sent). Let VD be any validated-dispersal protocol satisfying Definition 9 with round bound $T_2$ for the validity function "is a proof for $0$ or $1$ of the proof-creation instance". Then WeakBA, which runs PC for $T_1$ rounds, then VD on its output for $T_2$ rounds, and decides $v$ if the dispersed proofs are proofs for $v$ only and $\bot$ otherwise, satisfies Definition 3 (weak byzantine agreement) with round bound $T_1+T_2$:
--   1. every honest party outputs $0$, $1$ or $\bot$ by round $T_1+T_2$;
--   2. if all honest inputs equal $c$, every honest output is $c$; and
--   3. if an honest party outputs $v\ne\bot$, every honest output is $v$ or $\bot$.
--
--   This reduces weak agreement to proof creation and validated dispersal.
--
--   Differences from the source:
--   - generalization: WeakBA built from the paper's ProofCreation and ValidatedDispersion → WeakBA built from any protocols satisfying Definitions 8 (with proof soundness) and 9; reason: the proof uses only Definitions 5, 8 and 9; the paper's subprotocols are a special case
--   - reading: "relevant to the inputs" in Definition 8, i.e. Definition 5 → the hypothesis ProofSound: no proof for v derivable from the auxiliary knowledge and the sent messages when all honest inputs are 1 − v; reason: the proof of Theorem 3 invokes Definition 5 for the proofs of proof creation
--   - reading: "We properly define what a valid proof is in TODO" → validity = a proof for 0 or 1 in the sense of Definition 10; reason: the dangling reference points to Definition 10 (paper.md item 6)
--   - encoding: termination of the subprotocols → termination by explicit round bounds T₁, T₂, at which the next phase reads the output; reason: in a synchronous composition each phase ends at a fixed round
--   - generalization: a protocol run on its own → the guarantee holds against every admissible auxiliary adversary knowledge (anything without honest signatures of the instance's session subtree); reason: makes the specifications composable; the source's standalone run is the case aux = ∅
--   - reading: computationally unforgeable κ-bit signatures and a collision-resistant κ-bit hash (§4, p. 8) → idealized symbolic tokens: injective constructors sig p m, hash m; Dolev–Yao adversary; honest parties see tokens only through blinded shapes, equality tests and signature verification (with unbounded local computation they can recognise a token whose content they could construct themselves, but never obtain a signature they have not received); reason: every proof in the paper uses unforgeability and collision resistance as absolute facts (pp. 12, 16, 30) and no reduction appears (paper.md reading 1)
--   - generalization: a static adversary; rushing is not specified → a static rushing adversary: its round-r messages may depend on the honest round-r messages sent to corrupted parties; reason: a stronger adversary; every execution against a non-rushing adversary is one of these
--   - generalization: byzantine parties cannot forge signatures or invert the hash → the adversary may also open signature and hash tokens it holds (it still cannot create an honest party's signature); reason: a stronger adversary; the source's adversary is a special case
--   - encoding: messages of a given bit size; signatures and hashes of κ bits → symbolic terms of bit size: 2-bit tag per data node, a self-delimiting code for numbers, exactly κ bits per token; reason: the sizes of §4; constant per-node overheads do not change any instance's asymptotics
--   - encoding: instance tags on messages and signatures (§13) → every signature is domain-separated by the session number of its protocol instance; sub-instances get child sessions; reason: the §13 tags; replay across instances is excluded exactly as §13 intends
-- source:
--   Marc Dufay, Roger Wattenhofer, Optimal Subcubic Byzantine Agreement with Plain PKI, STOC 2027 submission #101 (October 2026), Theorem 3, p. 11 (WeakBA and Definitions 5, 8, 9, pp. 10–11)

import Mathlib
import Definitions.Def_SubcubicBA_PlainPKI_Model
import Definitions.Def_SubcubicBA_PlainPKI_Proofs
import Definitions.Def_SubcubicBA_PlainPKI_Compose

namespace SubcubicBA.PlainPKI

/-- Theorem 3 (p. 11). -/
theorem theorem_3 (PC VD : Protocol) (T₁ T₂ : ℕ → ℕ → ℕ → ℕ)
    (hPC : SolvesPC PC T₁) (hsound : ProofSound PC) (hVD : SolvesVD VD valWBA T₂) :
    SolvesWeakBA (weakBA PC T₁ VD T₂) (fun n t κ => T₁ n t κ + T₂ n t κ) := by sorry

end SubcubicBA.PlainPKI
