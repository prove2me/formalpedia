-- Prove2me | Theorems.Thm_ShannonSecrecy_perfect_secrecy_card_msg_le_card_key
-- name    : ShannonSecrecy.perfect_secrecy_card_msg_le_card_key
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T18:32:02.304718+00:00
-- url     : https://prove2.me/theorems/9f724ce3-3f08-4ec3-9ca3-eb8e9ed9a154
-- title:
--   Perfect secrecy requires at least as many keys as messages
-- statement:
--   **Shannon 1949, §10, p. 681.** *In a finite secrecy system with perfect secrecy, the number of different keys is at least as great as the number of messages.*
--
--   Shannon's reasoning: for a fixed key $i$, the map $T_i$ is a one-to-one correspondence between all the messages and some of the cryptograms, so there are at least as many cryptograms as messages. For perfect secrecy $P_M(E) = P(E) \neq 0$ for any of these cryptograms and any message, hence there is at least one key transforming any given message into any of them. All the keys leading from a fixed message to different cryptograms must be different, and therefore the number of different keys is at least as great as the number of messages.
--
--   This is the first quantitative limitation on perfect secrecy, and the origin of the one-time-pad requirement that the key be at least as long as the message.
--
--   **Formalization Note** "Number of messages" and "number of keys" are the cardinalities of the finite types $M$ and $K$; the conclusion is the inequality $|M| \le |K|$. No nonemptiness is assumed: a key set is automatically nonempty because the key probabilities sum to $1$, and keys of probability $0$ are allowed, so the counting argument must locate keys of positive probability.
-- source:
--   C. E. Shannon, "Communication Theory of Secrecy Systems", Bell System Technical Journal 28(4):656-715, 1949; https://doi.org/10.1002/j.1538-7305.1949.tb00928.x, p. 681 (Part II, §10 Perfect Secrecy, the paragraph following Theorem 6)

import Definitions.Def_shannon_secrecy_system

namespace ShannonSecrecy

theorem perfect_secrecy_card_msg_le_card_key
    {M K E : Type*} [Fintype M] [Fintype K] [Fintype E] [DecidableEq E]
    (C : Cipher M K E) (h : PerfectSecrecy C) :
    Fintype.card M ≤ Fintype.card K := by sorry

end ShannonSecrecy
