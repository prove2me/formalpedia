-- Prove2me | Theorems.Thm_TernarySync_Alphabet_previous_result_CHL19
-- name    : TernarySync.Alphabet.previous_result_CHL19
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-11T03:52:43.90818+00:00
-- url     : https://prove2.me/theorems/43fe11d4-6c0a-421f-9002-4fc35199d8ed
-- title:
--   §1.2, Previous result [CHL+19] — binary $\varepsilon$-synchronization strings have bounded length
-- statement:
--   For every fixed $0 \le \varepsilon < 1$, binary $\varepsilon$-synchronization strings have bounded length: there is an $M$ such that every $\varepsilon$-synchronization string over the alphabet $\{0,1\}$ has length at most $M$.
--
--   $$\forall\, 0 \le \varepsilon < 1\ \ \exists M\ \ \forall S \in \{0,1\}^*:\ S \text{ is an } \varepsilon\text{-synchronization string} \implies |S| \le M.$$
--
--   This is the second sentence of the previous result of Cheng, Haeupler, Li, Shahrasbi and Wu quoted in §1.2; it is the lower-bound half of the paper's main theorem: no fixed $\varepsilon < 1$ allows arbitrarily long binary synchronization strings, so three symbols are necessary.
--
--   **Formalization Note.** The binary alphabet is `Fin 2`.
--
--   Differences from the source:
--   - encoding: binary; bounded length → words over Fin 2; ∃ M, every ε-synchronization string has length ≤ M; reason: the meaning of 'bounded length' for the set of binary ε-synchronization strings
-- source:
--   Xu, Fu, Qiao, Tao, Synchronization Strings over a Ternary Alphabet, STOC 2027 submission (manuscript sha256 1b74ae6d…), p. 2 (PDF 3), §1.2, Previous result (Cheng, Haeupler, Li, Shahrasbi, and Wu [CHL+19]), second sentence

import Mathlib
import Definitions.Def_TernarySync_Alphabet_SyncString

set_option autoImplicit false

namespace TernarySync.Alphabet

/-- Previous result of Cheng, Haeupler, Li, Shahrasbi and Wu [CHL+19] (§1.2, p. 2), second
sentence: for every fixed `0 ≤ ε < 1`, binary `ε`-synchronization strings have bounded length. -/
theorem previous_result_CHL19 (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    ∃ M : ℕ, ∀ S : List (Fin 2), IsSyncString ε S → S.length ≤ M := by sorry

end TernarySync.Alphabet
