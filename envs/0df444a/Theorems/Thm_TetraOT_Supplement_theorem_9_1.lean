-- Prove2me | Theorems.Thm_TetraOT_Supplement_theorem_9_1
-- name    : TetraOT.Supplement.theorem_9_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:43:17.52519+00:00
-- url     : https://prove2.me/theorems/ee2fa8a0-57eb-4fe4-bfb7-1db7621fd3b7
-- title:
--   Theorem 9.1 — the Red-Black Protocol realizes ½ROT perfectly at rate $2/3$
-- statement:
--   Let $\rho$ be a uniform permutation of the four cards $\{0,1,2,3\} = \{L0,L1,R0,R1\}$, deal $(\rho(0),\rho(1))$ to Alice and $\rho(2)$ to Bob, and run the Red-Black Protocol (Fig. 21): Alice rejects a hand with both cards on the same side; otherwise she outputs $m_0m_1$ from Fig. 22 and Bob outputs $(s, m_s)$ from Fig. 24. The protocol is deterministic given $\rho$, and it perfectly realizes, against semi-honest parties, a ½ROT at rate $2/3$:
--
--   1. (correctness and rate) the joint law of the outputs is: reject for both with probability exactly $1/3$, and otherwise $\big((m_0,m_1),(s,m_s)\big)$ with $m_0,m_1,s$ independent uniform bits, independent of the reject event;
--   2. (semi-honest Alice) some simulator that sees only Alice's ideal output reproduces the joint law of her ordered hand and both outputs;
--   3. (semi-honest Bob) some simulator that sees only Bob's ideal output reproduces the joint law of his card, Alice's ok/reject message and both outputs.
--
--   The protocol is a simpler rejection-sampling alternative to the Tetrahedral Protocol, which never rejects.
--
--   **Formalization Note** Security is the published perfect standalone simulation notion; "rate $2/3$" is the acceptance probability, fixed by the ideal functionality.
--
--   Differences from the source:
--   - reading: "securely against semi-honest adversaries" / "perfectly secure against semi-honest adversaries" / "information-theoretically secure for honest-but-curious parties" (§2: "perfect conditional independence of messages given outputs. Isolated Real-Ideal simulations") → the published TetraOT.PerfectSemiHonestRealizes: equal output laws, and for each party a simulator seeing only that party's ideal output that reproduces the joint law of (view, both outputs); reason: the notion §2 names and the one the live mission's Theorem 4.1 uses; perfect and standalone
--   - reading: the parties' views → Alice's view is her ordered hand (ρ(0), ρ(1)); Bob's view is (ρ(2), ok/reject); reason: Alice receives no message and is deterministic; the only message is ok/reject (Fig. 26)
--   - reading: implements ½ROT … with rate 2/3 → ideal law idealRB: (none, none) with probability exactly 1/3, else (some (m₀, m₁), some (s, m_s)) ∼ idealROT independent of the reject event; reason: rate 2/3 is the acceptance probability; the proof says reject occurs with probability 1/3 independently of any bits
--   - encoding: reject: both parties quit (Fig. 21, step 3) → both outputs are none; reason: an optional output records the quit; same runs
--   - encoding: cards L0, L1, R0, R1 (Fig. 20); bits m₀m₁ → Fin 4 with 0 = L0, 1 = L1, 2 = R0, 3 = R1; Booleans with true = 1; the unreachable diagonal of Alice's table set to none; reason: Fig. 20's labeling; no deal gives Alice two equal cards
-- source:
--   Beaver, Correlated Group Interactions: Founding Cryptography on S4 and Sn, STOC 2027 submission (preprint, sha256 3dc88c598213707cd4cd52311a9b058999deef19d5aa9eed05208ba8092d65b7), Theorem 9.1, p.10, with Figs. 20–26, pp.10–11 (p. = PDF page; the PDF has no printed page numbers)

import Mathlib
import Definitions.Def_TetraOT_tetrahedralRun
import Definitions.Def_TetraOT_idealROT
import Definitions.Def_TetraOT_PerfectSemiHonestRealizes
import Definitions.Def_TetraOT_Supplement_redBlackAliceTable
import Definitions.Def_TetraOT_Supplement_redBlackBobTable
import Definitions.Def_TetraOT_Supplement_redBlackRun
import Definitions.Def_TetraOT_Supplement_idealRB

set_option autoImplicit false

namespace TetraOT.Supplement

open TetraOT

/-- **Theorem 9.1 (Red-Black OT)** (Beaver, *Correlated Group Interactions: Founding Cryptography on S4 and Sn*, STOC 2027 submission (held preprint, sha256 3dc88c59…92d65b7), Theorem 9.1, p.10, with Figs. 20–26, pp.10–11; p. = PDF page,
the PDF has no printed page numbers): "Dealing 2 cards to Alice and 1 card to Bob from a fully-shuffled
deck of four unique cards and using the Red-Black Protocol in Fig. 21 implements ½ROT with a
deterministic protocol, perfectly secure against semi-honest adversaries, with rate 2/3."

With `ρ` uniform on `S₄`, Alice holding `(ρ(0), ρ(1))` and Bob holding `ρ(2)` (cards `0, 1, 2, 3` =
`L0, L1, R0, R1`), Alice rejecting a same-side hand and otherwise reading `m₀m₁` off Fig. 22, and Bob
reading `(s, m_s)` off Fig. 24, the protocol perfectly realizes `idealRB` against a semi-honest Alice
and a semi-honest Bob:
1. the joint law of the outputs is: `(none, none)` (reject) with probability exactly `1/3`, and
   otherwise a random 1-of-2 oblivious transfer `(some (m₀, m₁), some (s, m_s))` with `m₀, m₁, s`
   independent uniform bits, independent of the reject event;
2. a simulator that sees only Alice's ideal output reproduces the joint law of (Alice's ordered hand,
   both outputs);
3. a simulator that sees only Bob's ideal output reproduces the joint law of (Bob's card and Alice's
   accept/reject message, both outputs).

**Formalization Note.** "Rate 2/3" is the acceptance probability, pinned by clause 1. "Deterministic" is
structural: the run is a function of `ρ`. Bits are `Bool` with `true` = 1. -/
theorem theorem_9_1 :
    PerfectSemiHonestRealizes deal rbViewA rbViewB rbAliceOut rbBobOut idealRB := by sorry

end TetraOT.Supplement
