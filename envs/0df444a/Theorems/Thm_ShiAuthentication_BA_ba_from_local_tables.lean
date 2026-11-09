-- Prove2me | Theorems.Thm_ShiAuthentication_BA_ba_from_local_tables
-- name    : ShiAuthentication.BA.ba_from_local_tables
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:17:04.38787+00:00
-- url     : https://prove2.me/theorems/65f85996-79a9-4892-8a9a-8d62bbc3c572
-- title:
--   Theorem 4.6 — $\Pi_{\mathrm{BA}}$: $5(t+1)$ rounds, polynomial local computation, $O(n^3(t+1)\kappa)$ honest communication
-- statement:
--   The deterministic phase-king Protocol 3, Π_BA, uses only local key tables and has code independent of G. It has exactly 5(t+1) rounds and uniform polynomial local computation. In particular a single finite multi-stack Turing machine computes evaluated outgoing messages and decisions from bounded channel prefixes, including signature processing and general maximum matching; oversized adversarial packets do not enlarge the local work budget.
--
--   There is an absolute constant C, fixed before n,t,G, the encoding budget κ, session, keys, inputs, faults and trace, such that for every n≥3, n>2t and every G satisfying the three-set condition, Π_BA solves Byzantine agreement. In every legal execution with compatible encoding budget κ and at most t faults, its total honest-sent communication, over all rounds, satisfies
--   $$B_H\le C n^3(t+1)\kappa.$$
--   Here B_H is the sum of actual binary `encMsg` lengths; no numeral for C is asserted. Every finite injective key assignment admits a compatible budget, and arbitrary adversarial terms remain allowed. This gives the full construction and resource guarantees used by the characterization.
--
--   Differences from the source:
--   - encoding: the finite party set P and the operational model of §3.1 → Fin n, symbolic terms, capability-restricted honest expressions and Dolev–Yao adversary derivability in synchronous traces; reason: relabeling and an operational representation; authentication edges never restrict communication
--   - encoding: distinct protocol/session/call identifiers and designated sender in signed data → a public fresh root session, optional designated sender, protocol tag, phase, subcall, message type, signer and optional public graph; the scheduled round is determined by these fields; reason: all invocations in a root execution have distinct signed contexts, including both Confirm calls and successive BA phases
--   - reading: the adversary may observe all honest messages → all honest messages in current and earlier rounds are available before faulty sends; reason: the literal rushing convention on p.15
--   - reading: idealized signatures following Dolev–Yao, with no separate statement about revealing their signed message → the signed message can be extracted from an observed signature; reason: the Dolev–Yao reading; no capability or unobserved signature can be extracted
--   - encoding: keys and identifiers have O(κ) size, and κ bounds signature size → a public compatible word budget bounds binary designated-key and identifier codes; correctness covers every such budget and session, with unbounded adversarial strings; reason: every finite injective key assignment and session admits arbitrarily large compatible budgets; the bounded-depth signature codec changes κ by a fixed absolute factor only
--   - encoding: Protocol 1 messages have prescribed O(κ) and O(nκ) formats; invalid packets/records are ignored → concrete directLimit and forwardLimit envelopes under the shared binary codec, with prefix rejection of oversized packets; reason: fixed format constants implement the source convention; compatible honest messages fit, while arbitrary adversarial messages remain allowed
--   - encoding: polynomial local computation → one multi-stack Turing machine computes evaluated sends and decisions from bounded channel prefixes; preprocessing reads and retained history are polynomial in n,t,κ; reason: this charges parsing, signing/verification, copying, expression evaluation and matching, and prevents oversized adversarial packets from enlarging the work budget
--   - generalization: a single protocol for each fixed n,t → one protocol, one machine and one polynomial uniformly for all n,t and compatible encodings; reason: specializing n,t gives every source instance
--   - encoding: 5(t+1) rounds → SolvesBA with this public bound and ExactBARounds, with no decision before that bound; reason: the construction uses the exact fixed schedule of Protocol 3
--   - encoding: O(n³(t+1)κ) honest communication with encoding conventions fixed once → actual encMsg bit counts and a uniform existential natural constant C; reason: the O(κ) representation overhead is fixed before all varying instances; the paper supplies no numerical coefficient
--   - encoding: t+1 distinct kings in a fixed public order → parties 0 through t; reason: relabeling by any graph-independent public order
-- source:
--   Kecheng Shi, STOC 2027 submission #203 (October 2026), Theorem 4.6, p. 21, with its proof pp. 21–22 (Protocol 3, p. 21)

import Definitions.Def_ShiAuthentication_BA_Protocols
import Definitions.Def_ShiAuthentication_BA_Cost

set_option autoImplicit false

namespace ShiAuthentication.BA

/-- **Theorem 4.6 (BA from local tables)**, pp. 21–22. The deterministic protocol `Π_BA`
(Protocol 3), whose code does not depend on `G` and uses only each party's initial key table,
(1) has polynomial local computation (one Turing machine and one polynomial for all parameters),
and there is an absolute constant `C` such that for all `n ≥ 3`, `n > 2t`, and every `G`
satisfying the three-set condition,
(2) `Π_BA` solves Byzantine agreement with `5(t + 1)` rounds, and
(3) in every admissible execution the total communication sent by honest parties is at most
`C · n³ (t + 1) κ` bits, for every source-compatible encoding budget `κ` and fresh session.
The measure is actual `encMsg` bit length, and malformed oversized packets are discarded. -/
theorem ba_from_local_tables :
    PolyTimeLocal PiBA ∧ PiBA.ExactBARounds ∧
    ∃ C : ℕ, ∀ n t : ℕ, 3 ≤ n → 2 * t < n → ∀ G : AuthGraph n, ThreeSetCondition G t →
      SolvesBA PiBA .localTables t G (5 * (t + 1)) ∧
      ∀ (session κ : ℕ) (vk : Fin n → ℕ), Function.Injective vk →
        ∀ (b : Fin n → Bool) (F : Finset (Fin n)), F.card ≤ t →
        (baSetup .localTables G t vk b F session κ).EncodingOK →
        ∀ tr : Trace n, IsRun PiBA (baSetup .localTables G t vk b F session κ) tr →
        ∀ R : ℕ, honestBits (baSetup .localTables G t vk b F session κ) tr R ≤ C * n ^ 3 * (t + 1) * κ := by sorry

end ShiAuthentication.BA
