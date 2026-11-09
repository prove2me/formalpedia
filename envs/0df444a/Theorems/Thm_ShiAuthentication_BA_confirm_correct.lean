-- Prove2me | Theorems.Thm_ShiAuthentication_BA_confirm_correct
-- name    : ShiAuthentication.BA.confirm_correct
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:14:51.09647+00:00
-- url     : https://prove2.me/theorems/bfde96ce-8ec7-42b3-8bf3-af66437093c9
-- title:
--   Lemma 4.4 — validity and weak consistency of $\Pi_{\mathrm{Confirm}}$
-- statement:
--   Let n≥3, n>2t, and let G satisfy the three-set condition. For any inputs b_p, any injective designated-key assignment, any compatible encoding budget and fresh session, any static fault set F of size at most t and any legal execution of the two-round local-table Protocol 1:
--
--   1. If every honest input is b, every honest party outputs b.
--   2. Any two honest non-⊥ outputs are equal.
--
--   Equivalently, for the honest parties H,
--   $$ (\forall p\in H,\ b_p=b)\Longrightarrow(\forall p\in H,\ o_p=b),\qquad
--    o_p,o_q\ne\bot\Longrightarrow o_p=o_q\quad(p,q\in H).$$
--   The output is each party's input bit or ⊥. This validity and weak consistency primitive is used by graded agreement.
--
--   Differences from the source:
--   - encoding: the finite party set P and the operational model of §3.1 → Fin n, symbolic terms, capability-restricted honest expressions and Dolev–Yao adversary derivability in synchronous traces; reason: relabeling and an operational representation; authentication edges never restrict communication
--   - encoding: distinct protocol/session/call identifiers and designated sender in signed data → a public fresh root session, optional designated sender, protocol tag, phase, subcall, message type, signer and optional public graph; the scheduled round is determined by these fields; reason: all invocations in a root execution have distinct signed contexts, including both Confirm calls and successive BA phases
--   - reading: the adversary may observe all honest messages → all honest messages in current and earlier rounds are available before faulty sends; reason: the literal rushing convention on p.15
--   - reading: idealized signatures following Dolev–Yao, with no separate statement about revealing their signed message → the signed message can be extracted from an observed signature; reason: the Dolev–Yao reading; no capability or unobserved signature can be extracted
--   - encoding: keys and identifiers have O(κ) size, and κ bounds signature size → a public compatible word budget bounds binary designated-key and identifier codes; correctness covers every such budget and session, with unbounded adversarial strings; reason: every finite injective key assignment and session admits arbitrarily large compatible budgets; the bounded-depth signature codec changes κ by a fixed absolute factor only
--   - encoding: Protocol 1 messages have prescribed O(κ) and O(nκ) formats; invalid packets/records are ignored → concrete directLimit and forwardLimit envelopes under the shared binary codec, with prefix rejection of oversized packets; reason: fixed format constants implement the source convention; compatible honest messages fit, while arbitrary adversarial messages remain allowed
--   - encoding: two-round Protocol 1 with output bit or ⊥ → standalone local-table PiConfirm, Option Bool outputs, root call tag (0,0,0); reason: the protocol is represented directly, including output after two rounds
-- source:
--   Kecheng Shi, STOC 2027 submission #203 (October 2026), Lemma 4.4, p. 18 (Protocol 1, p. 19)

import Definitions.Def_ShiAuthentication_BA_Protocols

set_option autoImplicit false

namespace ShiAuthentication.BA

/-- **Lemma 4.4**, p. 18. Let `n ≥ 3`, `n > 2t`, and let `G` satisfy the three-set condition.
In every admissible execution of `Π_Confirm` (Protocol 1, local key tables) with injective
designated keys and at most `t` faults:
(i) validity — if all honest inputs equal `c`, every honest party outputs `c`;
(ii) weak consistency — any two honest non-`⊥` outputs are equal. -/
theorem confirm_correct (n t : ℕ) (hn : 3 ≤ n) (ht : 2 * t < n) (G : AuthGraph n)
    (hG : ThreeSetCondition G t) (vk : Fin n → ℕ) (hvk : Function.Injective vk)
    (b : Fin n → Bool) (F : Finset (Fin n)) (hF : F.card ≤ t) (session κ : ℕ)
    (henc : (baSetup .localTables G t vk b F session κ).EncodingOK) (tr : Trace n)
    (hrun : IsRun PiConfirm (baSetup .localTables G t vk b F session κ) tr) :
    (∀ c : Bool, (∀ j : Fin n, j ∉ F → b j = c) →
      ∀ j : Fin n, j ∉ F → Outputs PiConfirm (baSetup .localTables G t vk b F session κ) tr j (some c)) ∧
    (∀ j k : Fin n, j ∉ F → k ∉ F → ∀ c c' : Bool,
      Outputs PiConfirm (baSetup .localTables G t vk b F session κ) tr j (some c) →
      Outputs PiConfirm (baSetup .localTables G t vk b F session κ) tr k (some c') → c = c') := by sorry

end ShiAuthentication.BA
