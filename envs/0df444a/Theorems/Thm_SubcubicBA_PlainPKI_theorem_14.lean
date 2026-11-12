-- Prove2me | Theorems.Thm_SubcubicBA_PlainPKI_theorem_14
-- name    : SubcubicBA.PlainPKI.theorem_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:45:24.948919+00:00
-- url     : https://prove2.me/theorems/8d4c1c4b-98ca-4ed2-ac88-c3813798e9cc
-- title:
--   Theorem 14 — graded agreement from weak agreement
-- statement:
--   Let $W$ be any protocol satisfying weak byzantine agreement (Definition 3) with round bound $T$. Then GradedAgreement, which runs $v\leftarrow W(v_{in})$, sets $w=1$ if $v\in\{1,\bot\}$ and $w=0$ otherwise, runs $b\leftarrow W(w)$, and returns $(1,1)$ if $v=1$, $(1,0)$ if $b=1$, $(0,1)$ if $b=0$ and $(0,0)$ otherwise, satisfies graded agreement (Definition 11) with round bound $2T$:
--   1. every honest party outputs some $(v,g)\in\{0,1\}^2$ by round $2T$;
--   2. if all honest inputs equal $c$, every honest output is $(c,1)$; and
--   3. if an honest party outputs $(v,1)$, every honest party outputs $v$.
--
--   Graded agreement is the interface through which the Momose–Ren framework builds byzantine agreement.
--
--   Differences from the source:
--   - generalization: GradedAgreement over the paper's WeakAgreement → GradedAgreement over any protocol satisfying Definition 3 with round bound T; reason: the proof uses only Definition 3
--   - reading: Definition 11 validity: "only v can be decided with grade 1" → every honest output is (v, 1); reason: the proof of Theorem 14 establishes this, and Theorem 13 needs it: under the weaker reading graded agreement may output (c, 0) or (1 − c, 0) on unanimous input c, and a half with a byzantine majority then imposes 1 − c in the adoption step
--   - encoding: outputs (v, g) → the term pair (nat v) (nat g); the two weak agreement instances are sequential sub-instances 0 and 1; reason: same outputs
--   - generalization: a protocol run on its own → the guarantee holds against every admissible auxiliary adversary knowledge (anything without honest signatures of the instance's session subtree); reason: makes the specifications composable; the source's standalone run is the case aux = ∅
--   - reading: computationally unforgeable κ-bit signatures and a collision-resistant κ-bit hash (§4, p. 8) → idealized symbolic tokens: injective constructors sig p m, hash m; Dolev–Yao adversary; honest parties see tokens only through blinded shapes, equality tests and signature verification (with unbounded local computation they can recognise a token whose content they could construct themselves, but never obtain a signature they have not received); reason: every proof in the paper uses unforgeability and collision resistance as absolute facts (pp. 12, 16, 30) and no reduction appears (paper.md reading 1)
--   - generalization: a static adversary; rushing is not specified → a static rushing adversary: its round-r messages may depend on the honest round-r messages sent to corrupted parties; reason: a stronger adversary; every execution against a non-rushing adversary is one of these
--   - generalization: byzantine parties cannot forge signatures or invert the hash → the adversary may also open signature and hash tokens it holds (it still cannot create an honest party's signature); reason: a stronger adversary; the source's adversary is a special case
--   - encoding: messages of a given bit size; signatures and hashes of κ bits → symbolic terms of bit size: 2-bit tag per data node, a self-delimiting code for numbers, exactly κ bits per token; reason: the sizes of §4; constant per-node overheads do not change any instance's asymptotics
--   - encoding: instance tags on messages and signatures (§13) → every signature is domain-separated by the session number of its protocol instance; sub-instances get child sessions; reason: the §13 tags; replay across instances is excluded exactly as §13 intends
-- source:
--   Marc Dufay, Roger Wattenhofer, Optimal Subcubic Byzantine Agreement with Plain PKI, STOC 2027 submission #101 (October 2026), Theorem 14, p. 41 (GradedAgreement, p. 41; Definition 11, p. 40)

import Mathlib
import Definitions.Def_SubcubicBA_PlainPKI_Model
import Definitions.Def_SubcubicBA_PlainPKI_Proofs
import Definitions.Def_SubcubicBA_PlainPKI_Compose

namespace SubcubicBA.PlainPKI

/-- Theorem 14 (p. 41). -/
theorem theorem_14 (W : Protocol) (T : ℕ → ℕ → ℕ → ℕ) (hW : SolvesWeakBA W T) :
    SolvesGA (gradedAgreement W T) (fun n t κ => 2 * T n t κ) := by sorry

end SubcubicBA.PlainPKI
