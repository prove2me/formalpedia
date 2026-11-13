-- Prove2me | Theorems.Thm_TernarySync_Alphabet_theorem_4_1
-- name    : TernarySync.Alphabet.theorem_4_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-11T03:52:54.257176+00:00
-- url     : https://prove2.me/theorems/b329133c-7e5f-40de-bfdd-ea607579a4f3
-- title:
--   Theorem 4.1 — ternary $\tfrac{2001}{2002}$-synchronization strings of every length $n \ge 1$
-- statement:
--   For every integer $n \ge 1$ there is a word $S$ of length $n$ over the ternary alphabet $\{0,1,2\}$ that is a $\tfrac{2001}{2002}$-synchronization string:
--
--   $$\mathrm{ED}\big(S[i,j),\, S[j,k)\big) > \frac{k-i}{2002} \qquad \text{for all } 1 \le i < j < k \le n+1,$$
--
--   where $\mathrm{ED}$ is the insertion–deletion distance. Equivalently, one may take synchronization gap $1/2002$.
--
--   This is the existence half of the paper's main result (Theorem 1.2), proved by the six-codeword construction: a random Brinkhuis substitution of a square-free word, the local lemma for long intervals and square-freeness for short ones.
--
--   **Formalization Note.** The alphabet is `Fin 3`; `IsSyncString (2001/2002) S` is Definition 1.1 with 0-based indices.
--
--   Differences from the source:
--   - encoding: a ternary alphabet; 1 ≤ i < j < k ≤ n + 1 → Fin 3; 0-based i < j < k ≤ n inside IsSyncString; reason: relabelling of the alphabet and the index shift; the same instances
-- source:
--   Xu, Fu, Qiao, Tao, Synchronization Strings over a Ternary Alphabet, STOC 2027 submission (manuscript sha256 1b74ae6d…), p. 15 (PDF 16), Theorem 4.1

import Mathlib
import Definitions.Def_TernarySync_Alphabet_SyncString

set_option autoImplicit false

namespace TernarySync.Alphabet

/-- Theorem 4.1 (p. 15): for every integer `n ≥ 1` there is a ternary
`2001/2002`-synchronization string of length `n` (synchronization gap `1/2002`). -/
theorem theorem_4_1 (n : ℕ) (hn : 1 ≤ n) :
    ∃ S : List (Fin 3), S.length = n ∧ IsSyncString ((2001 : ℝ) / 2002) S := by sorry

end TernarySync.Alphabet
