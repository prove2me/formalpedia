-- Prove2me | Theorems.Thm_ShiAuthentication_BA_main_theorem_1
-- name    : ShiAuthentication.BA.main_theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:16:22.7591+00:00
-- url     : https://prove2.me/theorems/993ee589-a464-44d9-8d82-0fd4abb58cd8
-- title:
--   Main Theorem 1 — exact graph characterization of Byzantine agreement
-- statement:
--   Let n≥3, 0≤t<n, and let G be a loopless authentication graph on the party set P. In both the public-graph and local-key-table settings,
--   $$\text{BA is possible on }G\quad\Longleftrightarrow\quad n>2t\ \text{and the three-set condition holds}.$$
--   The condition means that for every three pairwise disjoint A,B,C⊆P with
--   $$n-2t\le|A|,|B|,|C|\le t,\qquad |A|+|B|+|C|\ge2n-3t,$$
--   there is x∈C with V_x∩A≠∅ and V_x∩B≠∅. The sets need not cover P. At n=2t+1, BA is possible exactly when G is complete; at n≤2t it is impossible.
--
--   Moreover, a single deterministic protocol using only local tables, with code independent of G, has uniform polynomial local computation and exactly 5(t+1) rounds on every qualifying graph. Its actual outgoing messages and decisions are computable by one finite Turing machine from bounded channel prefixes, with arbitrary malformed adversarial traffic allowed.
--
--   Feasibility is operational: the protocol must achieve termination, agreement and unanimous-honest-input validity with zero error for every input, injective designated-key assignment, compatible encoding budget and fresh session, fault set of size at most t and admissible rushing adversary. All finite assignments are represented, since they admit arbitrarily large compatible budgets. Feasibility is never defined by the graph criterion. The result characterizes the initial authentication needed for agreement.
--
--   Differences from the source:
--   - encoding: the finite party set P and the operational model of §3.1 → Fin n, symbolic terms, capability-restricted honest expressions and Dolev–Yao adversary derivability in synchronous traces; reason: relabeling and an operational representation; authentication edges never restrict communication
--   - encoding: distinct protocol/session/call identifiers and designated sender in signed data → a public fresh root session, optional designated sender, protocol tag, phase, subcall, message type, signer and optional public graph; the scheduled round is determined by these fields; reason: all invocations in a root execution have distinct signed contexts, including both Confirm calls and successive BA phases
--   - reading: the adversary may observe all honest messages → all honest messages in current and earlier rounds are available before faulty sends; reason: the literal rushing convention on p.15
--   - reading: idealized signatures following Dolev–Yao, with no separate statement about revealing their signed message → the signed message can be extracted from an observed signature; reason: the Dolev–Yao reading; no capability or unobserved signature can be extracted
--   - encoding: keys and identifiers have O(κ) size, and κ bounds signature size → a public compatible word budget bounds binary designated-key and identifier codes; correctness covers every such budget and session, with unbounded adversarial strings; reason: every finite injective key assignment and session admits arbitrarily large compatible budgets; the bounded-depth signature codec changes κ by a fixed absolute factor only
--   - generalization: arbitrary finite communication and local computation for deterministic protocols → impossibility also excludes arbitrary deterministic function rules, including noncomputable ones; reason: all finite programs are included; the construction separately supplies a finite polynomial-time machine
--   - encoding: Protocol 1 messages have prescribed O(κ) and O(nκ) formats; invalid packets/records are ignored → concrete directLimit and forwardLimit envelopes under the shared binary codec, with prefix rejection of oversized packets; reason: fixed format constants implement the source convention; compatible honest messages fit, while arbitrary adversarial messages remain allowed
--   - encoding: polynomial local computation → one multi-stack Turing machine computes evaluated sends and decisions from bounded channel prefixes; preprocessing reads and retained history are polynomial in n,t,κ; reason: this charges parsing, signing/verification, copying, expression evaluation and matching, and prevents oversized adversarial packets from enlarging the work budget
--   - generalization: a single protocol for each fixed n,t → one protocol, one machine and one polynomial uniformly for all n,t and compatible encodings; reason: specializing n,t gives every source instance
--   - encoding: 5(t+1) rounds → SolvesBA with this public bound and ExactBARounds, with no decision before that bound; reason: the construction uses the exact fixed schedule of Protocol 3
--   - encoding: public-graph and local-table feasibility together with a uniform protocol across G → the iff is asserted for both modes, and the uniform code is quantified before G; reason: pointwise existence alone cannot express code independence from G; the separate uniform construction supplies it
--   - generalization: Main Theorem 1 on p.3 → also includes the complete-graph boundary and n≤2t impossibility from Theorem 4.1 p.17; reason: these are the stated consequences in the source restatement; deleting them recovers the p.3 statement
-- source:
--   Kecheng Shi, STOC 2027 submission #203 (October 2026), Main Theorem 1, p. 3; restated as Theorem 4.1, p. 17 (with the n = 2t + 1 and n ≤ 2t consequences)

import Definitions.Def_ShiAuthentication_BA_Cost

set_option autoImplicit false

namespace ShiAuthentication.BA

/-- **Main Theorem 1 (BA characterization)**, p. 3, restated with its boundary consequences as
Theorem 4.1, p. 17. For `n ≥ 3`, `0 ≤ t < n` and every loopless authentication graph `G`, in the
public-graph setting and in the local-table setting:
Byzantine agreement is possible on `G` iff `n > 2t` and `G` satisfies the three-set condition;
for `n = 2t + 1` it is possible iff `G` is the complete directed graph; for `n ≤ 2t` it is
impossible. Moreover a single deterministic protocol, using only each party's local key table and
not depending on `G`, has polynomial local computation and solves Byzantine agreement with
`5(t + 1)` rounds on every graph satisfying the condition. -/
theorem main_theorem_1 :
    (∀ n t : ℕ, 3 ≤ n → t < n → ∀ (G : AuthGraph n) (mode : Knowledge),
      (BAPossible mode t G ↔ (2 * t < n ∧ ThreeSetCondition G t)) ∧
      (n = 2 * t + 1 → (BAPossible mode t G ↔ G.IsComplete)) ∧
      (n ≤ 2 * t → ¬ BAPossible mode t G)) ∧
    ∃ P : Protocol Bool, PolyTimeLocal P ∧ P.ExactBARounds ∧
      ∀ n t : ℕ, 3 ≤ n → t < n → ∀ G : AuthGraph n, 2 * t < n → ThreeSetCondition G t →
        SolvesBA P .localTables t G (5 * (t + 1)) := by sorry

end ShiAuthentication.BA
