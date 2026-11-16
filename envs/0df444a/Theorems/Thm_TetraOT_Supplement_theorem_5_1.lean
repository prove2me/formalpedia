-- Prove2me | Theorems.Thm_TetraOT_Supplement_theorem_5_1
-- name    : TetraOT.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:42:34.553011+00:00
-- url     : https://prove2.me/theorems/7c3ee76a-aca7-4a5a-8b08-1cc50a12af26
-- title:
--   Theorem 5.1 — one ½ROT realizes a $(2,1;1)$ deal (corrected: Alice's message $M$ is announced to Bob)
-- statement:
--   Consider the inverted Tetrahedral Protocol (Fig. 10). Alice picks an ordered hand $(a,b)$ of two distinct cards of $\{0,1,2,3\}$ uniformly at random, computes $(M, m_0m_1) = A(a,b)$ with her Tetrahedral table, sends $M$ to Bob, and feeds $(m_0,m_1)$ into a single random 1-of-2 oblivious transfer whose selection bit $s$ is uniform and independent. Bob receives $(s, m_s)$ and sets $c = B^{-1}(M, (s,m_s))$ (Fig. 8).
--
--   Then the protocol perfectly realizes, against semi-honest parties, the $(2,1;1)$ deal in which Bob also learns $M$:
--
--   1. (correctness) the joint law of $\big((a,b), (c, M)\big)$ is that of $\big((\rho(0),\rho(1)), (\rho(2), A(\rho(0),\rho(1))_1)\big)$ for a uniform permutation $\rho$ of $\{0,1,2,3\}$; in particular $((a,b),c)$ is a uniform $(2,1;1)$ deal;
--   2. (semi-honest Alice) some simulator that sees only Alice's ideal output $(a,b)$ reproduces the joint law of Alice's view (her hand) and both outputs;
--   3. (semi-honest Bob) some simulator that sees only Bob's ideal output $(c, M)$ reproduces the joint law of Bob's view $(M, (s, m_s))$ and both outputs.
--
--   This is the reduction in the reverse direction that shows the Tetrahedral Protocol extracts the optimal number (one) of oblivious transfers from a $(2,1;1)$ deal.
--
--   **Formalization Note** Security is the published perfect standalone simulation notion. The oblivious transfer is an ideal channel inside the randomness (the OT-hybrid model); Alice receives nothing from it.
--
--   Differences from the source:
--   - reading: "securely against semi-honest adversaries" / "perfectly secure against semi-honest adversaries" / "information-theoretically secure for honest-but-curious parties" (§2: "perfect conditional independence of messages given outputs. Isolated Real-Ideal simulations") → the published TetraOT.PerfectSemiHonestRealizes: equal output laws, and for each party a simulator seeing only that party's ideal output that reproduces the joint law of (view, both outputs); reason: the notion §2 names and the one the live mission's Theorem 4.1 uses; perfect and standalone
--   - reading: the parties' views → Alice's view is her ordered hand (a, b); Bob's view is (M, (s, m_s)); reason: in the OT-hybrid model Alice receives nothing, and M and m₀m₁ are functions of her hand; Bob receives exactly M and the channel output
--   - reading: Alice chooses ρ(0), ρ(1) ←$ ({0123} choose 2) → Alice's ordered hand uniform over the 12 ordered pairs of distinct cards; reason: Fig. 9 lists the 12 ordered rows ρ_A, each chosen at random, and the deal result is the ordered pair ρ(0)ρ(1); a uniform unordered pair in uniform order is the same law
--   - encoding: Bob's result (y₀, y₁) ∈ {0•, 1•, •0, •1} → the pair (s, m_s) of Booleans, true = 1; reason: one-to-one recoding (right dot = s = 0, Fig. 5 caption), as in the published bobTable
--   - correction: the protocol implements a (2,1;1) deal (Bob's ideal output: his card c alone) → the ideal functionality also gives Bob Alice's message M (idealDealM); Bob's output is (c, M); reason: as printed the claim is false against a semi-honest Bob: with c = 0 and M = Y Alice's hand is {1,2} or {2,3}, never {1,3}, while a (2,1;1) deal gives each of the three hands probability 1/3 given c = 0, so no simulator from c alone reproduces Bob's view; Bob's view is in bijection with (c, M), so announcing M is the minimal correction; correctness (the deal marginal) and Alice's side are at full strength
--   - encoding: a single (²₁)ROT channel (Fig. 10: ½ROT) → an ideal channel in the OT-hybrid model: s is a uniform bit of the randomness, independent of Alice's hand, and Bob receives (s, m_s); reason: the ½ROT of Fig. 10 takes Alice's bits and a random selection bit; modelling it as an ideal channel is the hybrid model the theorem is about
-- source:
--   Beaver, Correlated Group Interactions: Founding Cryptography on S4 and Sn, STOC 2027 submission (preprint, sha256 3dc88c598213707cd4cd52311a9b058999deef19d5aa9eed05208ba8092d65b7), Theorem 5.1, p.5, with Figs. 7–10, pp.4–5 (p. = PDF page; the PDF has no printed page numbers)

import Mathlib
import Definitions.Def_TetraOT_Msg
import Definitions.Def_TetraOT_aliceTable
import Definitions.Def_TetraOT_tetrahedralRun
import Definitions.Def_TetraOT_PerfectSemiHonestRealizes
import Definitions.Def_TetraOT_Supplement_bobInvTable
import Definitions.Def_TetraOT_Supplement_reverseRun
import Definitions.Def_TetraOT_Supplement_idealDealM

set_option autoImplicit false

namespace TetraOT.Supplement

open TetraOT

/-- **Theorem 5.1 (reverse reduction: a (2, 1; 1) deal from one ½ROT), corrected** (Beaver, *Correlated Group Interactions: Founding Cryptography on S4 and Sn*, STOC 2027 submission (held preprint, sha256 3dc88c59…92d65b7), Theorem 5.1,
p.5; p. = PDF page, the PDF has no printed page numbers): "The protocol of Figs. 9, 7, 8, 10 implements a
(2, 1; 1) deal using a single (²₁)ROT securely against semi-honest adversaries."

Alice draws her ordered hand `(a, b)` uniformly among the 12 ordered pairs of distinct cards, computes
`(M, m₀m₁) = A(a, b)` (Fig. 2 / Fig. 7), sends `M` and feeds `(m₀, m₁)` into one ½ROT whose selection
bit `s` is uniform and independent; Bob receives `(s, m_s)` and sets `c = B⁻¹(M, (s, m_s))` (Fig. 8).
Then the protocol perfectly realizes, against a semi-honest Alice and a semi-honest Bob, the (2, 1; 1)
deal in which Bob also receives `M`:
1. the joint law of `((a, b), (c, M))` equals that of `((ρ(0), ρ(1)), (ρ(2), A(ρ(0), ρ(1)).1))` for
   `ρ` uniform on `S₄`; in particular `((a, b), c)` is a uniform (2, 1; 1) deal;
2. a simulator that sees only Alice's ideal output `(a, b)` reproduces the joint law of (Alice's view,
   both outputs);
3. a simulator that sees only Bob's ideal output `(c, M)` reproduces the joint law of (Bob's view
   `(M, (s, m_s))`, both outputs).

**Formalization Note.** The ½ROT is the ideal channel of the OT-hybrid model (the `Bool` in
`RevOmega`); Alice receives nothing from it. As printed (Bob's ideal output `c` alone), the claim is
false: with `c = 0` and `M = Y` Alice's hand is `{1, 2}` or `{2, 3}`, never `{1, 3}`, while a
(2, 1; 1) deal gives each of the three hands probability 1/3 given `c = 0`. Announcing `M` to Bob is
the minimal correction (Bob's view is in bijection with `(c, M)`); correctness and Alice's side are
unchanged. -/
theorem theorem_5_1 :
    PerfectSemiHonestRealizes revRandomness revViewA revViewB revAliceOut revBobOut idealDealM := by sorry

end TetraOT.Supplement
