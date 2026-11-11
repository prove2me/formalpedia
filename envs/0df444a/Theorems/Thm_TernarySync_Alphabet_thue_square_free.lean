-- Prove2me | Theorems.Thm_TernarySync_Alphabet_thue_square_free
-- name    : TernarySync.Alphabet.thue_square_free
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:52:46.432013+00:00
-- url     : https://prove2.me/theorems/d33d7c76-3cd4-43a1-8df5-89539d82b199
-- title:
--   §1.2, Thue's theorem [Thu06] — square-free ternary words of every length
-- statement:
--   Three symbols suffice for arbitrarily long square-free words: for every integer $n \ge 0$ there is a word $S$ of length $n$ over the alphabet $\{0,1,2\}$ that is square-free, i.e. no factor of $S$ has the form $XX$ with $X$ nonempty.
--
--   $$\forall n \ \exists S \in \{0,1,2\}^n:\ S \text{ is square-free}.$$
--
--   The paper cites Thue's classical theorem [Thu06] in §1.2 and uses it to choose the outer word $T$ of length $N = \lceil n/18 \rceil$ in the proof of Theorem 4.1 (for example, a prefix of Thue's infinite square-free word).
--
--   **Formalization Note.** The alphabet is `Fin 3`.
--
--   Differences from the source:
--   - reading: three symbols suffice for arbitrarily long square-free words → for every n there is a square-free word over Fin 3 of length exactly n; reason: equivalent, since a prefix of a square-free word is square-free; the exact-length form is the one the proof of Theorem 4.1 uses
-- source:
--   Xu, Fu, Qiao, Tao, Synchronization Strings over a Ternary Alphabet, STOC 2027 submission (manuscript sha256 1b74ae6d…), p. 2 (PDF 3), §1.2, Thue's theorem [Thu06]

import Mathlib
import Definitions.Def_TernarySync_Alphabet_SyncString

set_option autoImplicit false

namespace TernarySync.Alphabet

/-- Thue's theorem (§1.2, p. 2, [Thu06]): three symbols suffice for arbitrarily long
square-free words; for every `n` there is a square-free word of length `n` over `{0, 1, 2}`. -/
theorem thue_square_free (n : ℕ) :
    ∃ S : List (Fin 3), S.length = n ∧ IsSquareFree S := by sorry

end TernarySync.Alphabet
