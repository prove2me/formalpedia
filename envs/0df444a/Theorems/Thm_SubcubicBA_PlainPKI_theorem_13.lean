-- Prove2me | Theorems.Thm_SubcubicBA_PlainPKI_theorem_13
-- name    : SubcubicBA.PlainPKI.theorem_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:46:14.796951+00:00
-- url     : https://prove2.me/theorems/6711729c-aa69-483c-8deb-8ec833e934dd
-- title:
--   Theorem 13 — the Momose–Ren reduction
-- statement:
--   Let GA be any protocol satisfying graded agreement (Definition 11) with round bound $T_{GA}$, let Base be any protocol satisfying byzantine agreement (Definition 2) for fewer than $M$ parties with round bound $T_b$, and let $M\ge2$. Then ByzantineAgreement, which for $n\ge M$ parties runs graded agreement on all parties, recursive agreement on the first half $P_1$, a majority-adoption step, graded agreement again, recursive agreement on $P_2$ and a second adoption step, satisfies byzantine agreement for every $n$ and every $t<n/2$, with the round bound $T(n)=2T_{GA}(n)+T(\lfloor n/2\rfloor)+T(\lceil n/2\rceil)+2$ (and $T_b$ below $M$):
--   1. every honest party outputs a bit by round $T(n)$;
--   2. if all honest inputs equal $c$, every honest output is $c$; and
--   3. any two honest outputs are equal.
--
--   The halves may have a byzantine majority; at least one of them has an honest majority.
--
--   Differences from the source:
--   - generalization: ByzantineAgreement over the paper's GradedAgreement and an inefficient cubic protocol → over any protocols satisfying Definition 11 (bound T_GA) and Definition 2 below M (bound T_b); reason: the reduction uses only these specifications
--   - reading: Definition 11 validity: "only v can be decided with grade 1" → every honest output is (v, 1); reason: the proof of Theorem 14 establishes this, and Theorem 13 needs it: under the weaker reading graded agreement may output (c, 0) or (1 − c, 0) on unanimous input c, and a half with a byzantine majority then imposes 1 − c in the adoption step
--   - encoding: "Partition P into two halves P₁ and P₂"; recursive calls on the halves → P₁ = the first ⌊n/2⌋ parties, P₂ the rest; sub-instances on a half of size k use the fault bound ⌊(k − 1)/2⌋; M ≥ 2; reason: a fixed partition into halves as in Lemma 21; the fault bound is the largest t′ with 2t′ < k
--   - reading: "received the same o from a majority of P₁" → more than |P₁|/2 members of P₁ sent the bit o in the round after the recursive call; reason: majority is strict
--   - generalization: a protocol run on its own → the guarantee holds against every admissible auxiliary adversary knowledge (anything without honest signatures of the instance's session subtree); reason: makes the specifications composable; the source's standalone run is the case aux = ∅
--   - reading: computationally unforgeable κ-bit signatures and a collision-resistant κ-bit hash (§4, p. 8) → idealized symbolic tokens: injective constructors sig p m, hash m; Dolev–Yao adversary; honest parties see tokens only through blinded shapes, equality tests and signature verification (with unbounded local computation they can recognise a token whose content they could construct themselves, but never obtain a signature they have not received); reason: every proof in the paper uses unforgeability and collision resistance as absolute facts (pp. 12, 16, 30) and no reduction appears (paper.md reading 1)
--   - generalization: a static adversary; rushing is not specified → a static rushing adversary: its round-r messages may depend on the honest round-r messages sent to corrupted parties; reason: a stronger adversary; every execution against a non-rushing adversary is one of these
--   - generalization: byzantine parties cannot forge signatures or invert the hash → the adversary may also open signature and hash tokens it holds (it still cannot create an honest party's signature); reason: a stronger adversary; the source's adversary is a special case
--   - encoding: messages of a given bit size; signatures and hashes of κ bits → symbolic terms of bit size: 2-bit tag per data node, a self-delimiting code for numbers, exactly κ bits per token; reason: the sizes of §4; constant per-node overheads do not change any instance's asymptotics
--   - encoding: instance tags on messages and signatures (§13) → every signature is domain-separated by the session number of its protocol instance; sub-instances get child sessions; reason: the §13 tags; replay across instances is excluded exactly as §13 intends
-- source:
--   Marc Dufay, Roger Wattenhofer, Optimal Subcubic Byzantine Agreement with Plain PKI, STOC 2027 submission #101 (October 2026), Theorem 13, p. 41 (ByzantineAgreement, pp. 40–41; [24, Lemma 9])

import Mathlib
import Definitions.Def_SubcubicBA_PlainPKI_Model
import Definitions.Def_SubcubicBA_PlainPKI_Proofs
import Definitions.Def_SubcubicBA_PlainPKI_Compose

namespace SubcubicBA.PlainPKI

/-- Theorem 13 (p. 41; Momose–Ren, Lemma 9). -/
theorem theorem_13 (GA Base : Protocol) (TGA Tb : ℕ → ℕ → ℕ → ℕ) (M : ℕ) (hM : 2 ≤ M)
    (hGA : SolvesGA GA TGA) (hBase : SolvesBA Base Tb (fun n => n < M)) :
    SolvesBA (byzantineAgreement GA TGA Base Tb M) (baRounds TGA Tb M) (fun _ => True) := by sorry

end SubcubicBA.PlainPKI
