-- Prove2me | Theorems.Thm_TetraOT_theorem_4_1
-- name    : TetraOT.theorem_4_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-09T22:27:36.882032+00:00
-- url     : https://prove2.me/theorems/765284ab-f84d-44bb-961c-73a3d047b9aa
-- title:
--   Theorem 4.1 (Tetrahedral ROT) — perfect semi-honest random oblivious transfer from one $S_4$ deal
-- statement:
--   Shuffle a deck of four distinct cards $0,1,2,3$ by a uniformly random permutation $\rho \in S_4$. Alice receives the ordered hand $(\rho(0), \rho(1))$, Bob receives $\rho(2)$, and $\rho(3)$ is not seen. Alice reads $(M, m_0, m_1) = A(\rho(0), \rho(1))$ from her table (Fig. 2) and sends $M \in \{X,Y,Z\}$; Bob reads $(y_0, y_1) = B(M, \rho(2))$ from his table (Fig. 3), that is, a selection bit $s$ and a bit $y_s$.
--
--   **Theorem 4.1 (Tetrahedral ROT).** This protocol implements random 1-of-2 oblivious transfer $\binom{2}{1}\mathrm{ROT}$ perfectly securely against semi-honest adversaries. That is, with $\mathcal F_{\mathrm{ROT}}$ the law of $((m_0, m_1), (s, m_s))$ for independent uniform bits $m_0, m_1, s$:
--
--   1. the joint law of the real outputs $((m_0,m_1),(s,y_s))$ equals $\mathcal F_{\mathrm{ROT}}$;
--   2. there is a simulator that, given only Alice's ideal output $(m_0, m_1)$, samples a hand whose joint law with both ideal outputs equals the real joint law of (Alice's ordered hand, Alice's output, Bob's output);
--   3. there is a simulator that, given only Bob's ideal output $(s, m_s)$, samples a pair (card, message) whose joint law with both ideal outputs equals the real joint law of ($(\rho(2), M)$, Alice's output, Bob's output).
--
--   The protocol uses one message, no randomness beyond the deal, and produces one ROT per deal.
--
--   **Formalization Note** "Securely against semi-honest adversaries" is formalized as perfect standalone simulation-based security (`PerfectSemiHonestRealizes`), the reading the paper announces in §2. Bits are Booleans with $\texttt{true}=1$; `ρ i` is the paper's $\rho(i)$.
--
--   Differences from the source:
--   - reading: "securely against semi-honest adversaries" (§2: "perfect conditional independence of messages given outputs. Isolated Real-Ideal simulations") → perfect standalone simulation-based security: equal output laws, and for each party a simulator seeing only that party's ideal output that reproduces the joint law of (view, both outputs); reason: the standard definition (Goldreich Vol. II, Def. 7.2.1) and the form §2 names; since each view determines its party's output, it is equivalent to §2's conditional independence together with correctness
--   - reading: the parties' views → Alice's view is her ordered hand $(\rho(0),\rho(1))$, Bob's view is $(\rho(2), M)$; reason: Alice receives no message and her message and output are functions of her hand; Bob's view is "produced by a particular $M$ and $\rho(2)$" (proof of Theorem 4.1)
--   - reading: $\binom{2}{1}\mathrm{ROT}$ → $m_0, m_1, s$ independent uniform bits, Alice outputs $(m_0, m_1)$, Bob outputs $(s, m_s)$; reason: Definition 2.5 gives this description for both $\tfrac12\mathrm{ROT}$ and $\binom{2}{1}\mathrm{ROT}$, and Fig. 1 calls the same protocol $\tfrac12\mathrm{ROT}$
--   - encoding: Bob's result $(y_0, y_1) \in \{0\bullet, 1\bullet, \bullet0, \bullet1\}$ → the pair $(s, m_s)$ of Booleans; reason: one-to-one recoding (right dot = $s = 0$, Fig. 5 caption)
--   - encoding: the diagonal cells "$\cdot$" of Fig. 2 → the fixed value $(X, 00)$; reason: a total function needs a value there and no deal reaches the diagonal, since $\rho(0) \ne \rho(1)$
-- source:
--   Beaver, Correlated Group Interactions: Founding Cryptography on S4 and Sn, STOC 2027 submission (preprint, sha256 3dc88c598213707cd4cd52311a9b058999deef19d5aa9eed05208ba8092d65b7), Theorem 4.1, p.3 (p. = PDF page; the PDF has no printed page numbers)

import Mathlib
import Definitions.Def_TetraOT_Msg
import Definitions.Def_TetraOT_aliceTable
import Definitions.Def_TetraOT_bobTable
import Definitions.Def_TetraOT_tetrahedralRun
import Definitions.Def_TetraOT_idealROT
import Definitions.Def_TetraOT_PerfectSemiHonestRealizes

set_option autoImplicit false

namespace TetraOT

/-- **Theorem 4.1 (Tetrahedral ROT)** (Beaver, *Correlated Group Interactions: Founding Cryptography on S4 and Sn*, STOC 2027 submission (held preprint, sha256 3dc88c59…92d65b7), Theorem 4.1, p.3; p. = PDF page, the PDF has no
printed page numbers): "The protocol of Fig.1 implements (²₁)ROT securely against semi-honest
adversaries."

With `ρ` uniform on `S₄`, Alice holding `(ρ(0), ρ(1))`, Bob holding `ρ(2)`, Alice looking up
`(M, m₀, m₁) = A(ρ(0), ρ(1))` in Fig. 2 and sending `M`, and Bob looking up `(y₀, y₁) = B(M, ρ(2))` in
Fig. 3, the protocol perfectly realizes the random 1-of-2 oblivious transfer of Definition 2.5 against a
semi-honest Alice and against a semi-honest Bob:
1. the joint law of the outputs `((m₀, m₁), (s, m_s))` is that of independent uniform bits
   `m₀, m₁, s`;
2. some simulator that sees only Alice's ideal output `(m₀, m₁)` reproduces the joint law of
   (Alice's ordered hand, Alice's output, Bob's output);
3. some simulator that sees only Bob's ideal output `(s, m_s)` reproduces the joint law of
   (Bob's card and the message `M`, Alice's output, Bob's output).

**Formalization Note.** "Securely against semi-honest adversaries" is perfect standalone
simulation-based security (`PerfectSemiHonestRealizes`; §2, p.2: "perfect conditional independence of
messages given outputs. Isolated Real-Ideal simulations"). Alice's view is her ordered hand (it
determines `M` and her output); Bob's view is `(ρ(2), M)`. Bob's output `(s, m_s)` encodes his
`(y₀, y₁)` ("b•" ↦ `(false, b)`, "•b" ↦ `(true, b)`); bits are `Bool` with `true` = 1. -/
theorem theorem_4_1 :
    PerfectSemiHonestRealizes deal viewA viewB aliceOut bobOut idealROT := by sorry

end TetraOT
