-- Prove2me | Theorems.Thm_TernarySync_Alphabet_theorem_1_2
-- name    : TernarySync.Alphabet.theorem_1_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:52:48.602601+00:00
-- url     : https://prove2.me/theorems/9a99ff1a-aefb-4a27-a5e3-e4bc3c4f00f0
-- title:
--   Theorem 1.2 — ternary $\tfrac{2001}{2002}$-synchronization strings of every length, and three is the minimum alphabet size
-- statement:
--   **(a)** For every integer $n \ge 1$ there is a ternary $\tfrac{2001}{2002}$-synchronization string of length $n$: a word $S \in \{0,1,2\}^n$ with
--
--   $$\mathrm{ED}\big(S[i,j),\, S[j,k)\big) > \Big(1 - \frac{2001}{2002}\Big)(k-i) \qquad \text{for all } 1 \le i < j < k \le n+1,$$
--
--   where $\mathrm{ED}$ is the insertion–deletion distance and $S[i,j) = S_i \cdots S_{j-1}$.
--
--   **(b)** Consequently, three is the minimum constant alphabet size supporting synchronization strings of all lengths for some fixed $\varepsilon < 1$: $3$ is the least $q \in \mathbb{N}$ such that, for some $0 \le \varepsilon < 1$, there is an $\varepsilon$-synchronization string of every length $n \ge 1$ over an alphabet of $q$ symbols.
--
--   Synchronization strings (Haeupler and Shahrasbi) let a receiver recover positions after insertions and deletions using labels from an alphabet independent of the message length. Four symbols were known to suffice and two not to; this theorem settles the open ternary case, with an explicit parameter.
--
--   **Formalization Note.** The alphabet of size $q$ is `Fin q`; clause (b) is `IsLeast` of the set of such $q$. `IsSyncString ε S` is Definition 1.1 with 0-based indices ($i < j < k \le |S|$).
--
--   Differences from the source:
--   - encoding: a ternary alphabet; an alphabet of size q; 1 ≤ i < j < k ≤ n + 1 → Fin 3 and Fin q; 0-based i < j < k ≤ n inside IsSyncString; reason: relabelling of the alphabet and the index shift; the same instances
--   - reading: three is the minimum constant alphabet size supporting synchronization strings of all lengths for some fixed ε < 1 → IsLeast {q | ∃ ε, 0 ≤ ε ∧ ε < 1 ∧ ∀ n ≥ 1, ∃ S : List (Fin q), S.length = n ∧ IsSyncString ε S} 3; reason: the alphabet is fixed independently of the length (Definition 1.1) and ε is fixed before n; 0 ≤ ε is Definition 1.1's range
-- source:
--   Xu, Fu, Qiao, Tao, Synchronization Strings over a Ternary Alphabet, STOC 2027 submission (manuscript sha256 1b74ae6d…), p. 2 (PDF 3), Theorem 1.2; existence: p. 15 (PDF 16), Theorem 4.1; minimality: p. 18 (PDF 19), proof of Theorem 1.2

import Mathlib
import Definitions.Def_TernarySync_Alphabet_SyncString

set_option autoImplicit false

namespace TernarySync.Alphabet

/-- Theorem 1.2 (p. 2). (a) For every integer `n ≥ 1` there is a ternary
`2001/2002`-synchronization string of length `n`. (b) Consequently, three is the minimum
alphabet size supporting synchronization strings of all lengths for some fixed `ε < 1`: `3` is
the least `q` such that for some `0 ≤ ε < 1` there is an `ε`-synchronization string of every
length `n ≥ 1` over `Fin q`. -/
theorem theorem_1_2 :
    (∀ n : ℕ, 1 ≤ n → ∃ S : List (Fin 3), S.length = n ∧ IsSyncString ((2001 : ℝ) / 2002) S) ∧
      IsLeast {q : ℕ | ∃ ε : ℝ, 0 ≤ ε ∧ ε < 1 ∧
        ∀ n : ℕ, 1 ≤ n → ∃ S : List (Fin q), S.length = n ∧ IsSyncString ε S} 3 := by sorry

end TernarySync.Alphabet
