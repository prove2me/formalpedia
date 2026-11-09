-- Prove2me | Theorems.Thm_ShiAuthentication_BA_broadcast_obstruction
-- name    : ShiAuthentication.BA.broadcast_obstruction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:10:01.369849+00:00
-- url     : https://prove2.me/theorems/dd322d8b-05da-4520-aff2-bd5fe809aa98
-- title:
--   Lemma 4.2 — broadcast obstruction from three indistinguishable executions
-- statement:
--   Let n≥3 and 0≤t<n, and let G be a loopless authentication graph on P. Suppose nonempty pairwise disjoint A,B,C⊆P satisfy
--   $$n-2t\le |A|,|B|,|C|\le t,\qquad |A|+|B|+|C|\ge2n-3t.$$
--   If S∈C and every x∈C satisfies
--   $$V_x\cap A=\varnothing\quad\text{or}\quad V_x\cap B=\varnothing,$$
--   no deterministic protocol solves Byzantine broadcast from S against at most t faults, even if honest parties are required only to output eventually. The assertion covers both graph-knowledge settings, every injective designated-key assignment, every compatible encoding budget and every fresh session, all inputs and all legal rushing adversaries. No public termination bound is assumed.
--
--   This is the obstruction used for necessity in the characterization.
--
--   Differences from the source:
--   - encoding: the finite party set P and the operational model of §3.1 → Fin n, symbolic terms, capability-restricted honest expressions and Dolev–Yao adversary derivability in synchronous traces; reason: relabeling and an operational representation; authentication edges never restrict communication
--   - encoding: distinct protocol/session/call identifiers and designated sender in signed data → a public fresh root session, optional designated sender, protocol tag, phase, subcall, message type, signer and optional public graph; the scheduled round is determined by these fields; reason: all invocations in a root execution have distinct signed contexts, including both Confirm calls and successive BA phases
--   - reading: the adversary may observe all honest messages → all honest messages in current and earlier rounds are available before faulty sends; reason: the literal rushing convention on p.15
--   - reading: idealized signatures following Dolev–Yao, with no separate statement about revealing their signed message → the signed message can be extracted from an observed signature; reason: the Dolev–Yao reading; no capability or unobserved signature can be extracted
--   - encoding: keys and identifiers have O(κ) size, and κ bounds signature size → a public compatible word budget bounds binary designated-key and identifier codes; correctness covers every such budget and session, with unbounded adversarial strings; reason: every finite injective key assignment and session admits arbitrarily large compatible budgets; the bounded-depth signature codec changes κ by a fixed absolute factor only
--   - generalization: arbitrary finite communication and local computation for deterministic protocols → impossibility also excludes arbitrary deterministic function rules, including noncomputable ones; reason: all finite programs are included; the construction separately supplies a finite polynomial-time machine
--   - generalization: BB(G,S,t) in the public-graph model of §3.1 → the obstruction is asserted in both knowledge settings; reason: local-table protocols are included in the public-graph impossibility claim
-- source:
--   Kecheng Shi, STOC 2027 submission #203 (October 2026), Lemma 4.2, p. 17

import Definitions.Def_ShiAuthentication_BA_Execution

set_option autoImplicit false

namespace ShiAuthentication.BA

/-- **Lemma 4.2 (Broadcast obstruction)**, p. 17. Let `n ≥ 3`, `0 ≤ t < n`, and let `A, B, C`
be nonempty, pairwise disjoint sets of parties with `n − 2t ≤ |A|, |B|, |C| ≤ t` and
`|A| + |B| + |C| ≥ 2n − 3t`. If `S ∈ C` and every `x ∈ C` has no verifier in `A` or no verifier
in `B` (condition (1)), then no deterministic protocol solves broadcast from `S` against `t`
faults on `G`, even if honest parties are only required to output eventually — in the
public-graph setting and in the local-table setting. -/
theorem broadcast_obstruction (n t : ℕ) (hn : 3 ≤ n) (ht : t < n) (G : AuthGraph n)
    (A B C : Finset (Fin n)) (hAne : A.Nonempty) (hBne : B.Nonempty) (hCne : C.Nonempty)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hAlo : (n : ℤ) - 2 * t ≤ A.card) (hBlo : (n : ℤ) - 2 * t ≤ B.card)
    (hClo : (n : ℤ) - 2 * t ≤ C.card)
    (hAhi : A.card ≤ t) (hBhi : B.card ≤ t) (hChi : C.card ≤ t)
    (hsum : 2 * (n : ℤ) - 3 * t ≤ (A.card : ℤ) + B.card + C.card)
    (S : Fin n) (hS : S ∈ C)
    (h1 : ∀ x ∈ C, G.verifiers x ∩ A = ∅ ∨ G.verifiers x ∩ B = ∅) :
    ∀ mode : Knowledge, ¬ ∃ P : Protocol Bool, SolvesBBEventually P mode t G S := by sorry

end ShiAuthentication.BA
