-- Prove2me | Theorems.Thm_ShiAuthentication_BA_graded_agreement_correct
-- name    : ShiAuthentication.BA.graded_agreement_correct
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:13:42.568043+00:00
-- url     : https://prove2.me/theorems/dd6b2b71-0690-4b24-8e79-188266a5bf17
-- title:
--   Lemma 4.5 — graded agreement from two calls of $\Pi_{\mathrm{Confirm}}$
-- statement:
--   Let n≥3, n>2t, and let G satisfy the three-set condition. Consider every legal execution of the four-round local-table Protocol 2, with arbitrary inputs, injective designated keys, compatible encoding budget and fresh session, and at most t static faults. Each honest party outputs a candidate c_p∈{0,1} and grade g_p∈{0,1}. Then:
--
--   1. If all honest inputs equal b, every honest output is (b,1).
--   2. If any honest party outputs (b,1), every honest party outputs (b,g) for some g∈{0,1}:
--   $$\exists p\in H:\ (c_p,g_p)=(b,1)\Longrightarrow\forall q\in H:\ c_q=b.$$
--   Both Confirm calls execute, and a grade set in the first call is retained. This is the graded agreement primitive of Protocol 3.
--
--   Differences from the source:
--   - encoding: the finite party set P and the operational model of §3.1 → Fin n, symbolic terms, capability-restricted honest expressions and Dolev–Yao adversary derivability in synchronous traces; reason: relabeling and an operational representation; authentication edges never restrict communication
--   - encoding: distinct protocol/session/call identifiers and designated sender in signed data → a public fresh root session, optional designated sender, protocol tag, phase, subcall, message type, signer and optional public graph; the scheduled round is determined by these fields; reason: all invocations in a root execution have distinct signed contexts, including both Confirm calls and successive BA phases
--   - reading: the adversary may observe all honest messages → all honest messages in current and earlier rounds are available before faulty sends; reason: the literal rushing convention on p.15
--   - reading: idealized signatures following Dolev–Yao, with no separate statement about revealing their signed message → the signed message can be extracted from an observed signature; reason: the Dolev–Yao reading; no capability or unobserved signature can be extracted
--   - encoding: keys and identifiers have O(κ) size, and κ bounds signature size → a public compatible word budget bounds binary designated-key and identifier codes; correctness covers every such budget and session, with unbounded adversarial strings; reason: every finite injective key assignment and session admits arbitrarily large compatible budgets; the bounded-depth signature codec changes κ by a fixed absolute factor only
--   - encoding: Protocol 1 messages have prescribed O(κ) and O(nκ) formats; invalid packets/records are ignored → concrete directLimit and forwardLimit envelopes under the shared binary codec, with prefix rejection of oversized packets; reason: fixed format constants implement the source convention; compatible honest messages fit, while arbitrary adversarial messages remain allowed
--   - encoding: four-round Protocol 2 and grades 0,1 → standalone local-table PiGBA with Bool grades and call tags (1,0,0),(1,0,1); reason: Bool represents exactly both grades; both source conclusion clauses are retained
-- source:
--   Kecheng Shi, STOC 2027 submission #203 (October 2026), Lemma 4.5, pp. 20–21 (Protocol 2, p. 20)

import Definitions.Def_ShiAuthentication_BA_Protocols

set_option autoImplicit false

namespace ShiAuthentication.BA

/-- **Lemma 4.5 (Graded agreement)**, pp. 20–21. Let `n ≥ 3`, `n > 2t`, and let `G` satisfy the
three-set condition. In every admissible execution of the four-round protocol `Π_GBA`
(Protocol 2, local key tables) with injective designated keys and at most `t` faults:
(i) validity — if all honest inputs equal `c`, every honest party outputs `(c, 1)`;
(ii) graded consistency — if some honest party outputs `(c, 1)`, every honest party outputs
`(c, g)` for some grade `g`. Grade `1` is `true`. -/
theorem graded_agreement_correct (n t : ℕ) (hn : 3 ≤ n) (ht : 2 * t < n) (G : AuthGraph n)
    (hG : ThreeSetCondition G t) (vk : Fin n → ℕ) (hvk : Function.Injective vk)
    (b : Fin n → Bool) (F : Finset (Fin n)) (hF : F.card ≤ t) (session κ : ℕ)
    (henc : (baSetup .localTables G t vk b F session κ).EncodingOK) (tr : Trace n)
    (hrun : IsRun PiGBA (baSetup .localTables G t vk b F session κ) tr) :
    (∀ c : Bool, (∀ j : Fin n, j ∉ F → b j = c) →
      ∀ j : Fin n, j ∉ F → Outputs PiGBA (baSetup .localTables G t vk b F session κ) tr j (c, true)) ∧
    (∀ j : Fin n, j ∉ F → ∀ c : Bool,
      Outputs PiGBA (baSetup .localTables G t vk b F session κ) tr j (c, true) →
      ∀ k : Fin n, k ∉ F → ∃ g : Bool, Outputs PiGBA (baSetup .localTables G t vk b F session κ) tr k (c, g)) := by sorry

end ShiAuthentication.BA
