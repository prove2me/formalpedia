-- Prove2me | Theorems.Thm_TernarySync_Alphabet_sync_square_free
-- name    : TernarySync.Alphabet.sync_square_free
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-11T03:52:57.68827+00:00
-- url     : https://prove2.me/theorems/1e7ca8af-e85e-44d5-a3a6-a157ffbfe7d8
-- title:
--   §2.1 — synchronization strings with $\varepsilon < 1$ are square-free; factors inherit both properties
-- statement:
--   Let $0 \le \varepsilon < 1$ and let $S$ be a word over any alphabet. Then:
--
--   1. if $S$ is an $\varepsilon$-synchronization string, then $S$ is square-free;
--   2. if $S$ is an $\varepsilon$-synchronization string, then so is every factor (contiguous subword) $F$ of $S$, with the same $\varepsilon$;
--   3. if $S$ is square-free, then so is every factor $F$ of $S$.
--
--   $$S \text{ is } \varepsilon\text{-synchronization} \implies S \text{ square-free}; \qquad F \text{ factor of } S:\ \ S \text{ has the property} \implies F \text{ has it}.$$
--
--   The paper records this right after Definition 2.1 ("By Definition 1.1, every synchronization string with $\varepsilon < 1$ is square-free. Factors, and in particular prefixes, inherit both properties with the same parameter."). Square-freeness is the reason short intervals are handled for free, and inheritance by prefixes lets the construction cut a long output down to length $n$.
--
--   **Formalization Note.** "Factor" is a contiguous sublist (`F <:+: S`); prefixes are a special case.
--
--   Differences from the source:
--   - reading: factors inherit both properties with the same parameter → two separate clauses: the synchronization property passes to factors with the same ε, and square-freeness passes to factors; reason: each property is inherited on its own; this is the plain reading of the sentence
--   - encoding: synchronization string with ε < 1 (Definition 1.1 fixes 0 ≤ ε < 1) → hypotheses 0 ≤ ε and ε < 1; reason: the range of Definition 1.1 written as binders
-- source:
--   Xu, Fu, Qiao, Tao, Synchronization Strings over a Ternary Alphabet, STOC 2027 submission (manuscript sha256 1b74ae6d…), p. 13 (PDF 14), §2.1, the paragraph after Definition 2.1

import Mathlib
import Definitions.Def_TernarySync_Alphabet_SyncString

set_option autoImplicit false

namespace TernarySync.Alphabet

/-- §2.1, after Definition 2.1 (p. 13): every `ε`-synchronization string with `0 ≤ ε < 1` is
square-free; and factors (contiguous subwords, in particular prefixes) inherit both properties,
the synchronization property with the same parameter `ε`. -/
theorem sync_square_free {α : Type*} (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) (S : List α) :
    (IsSyncString ε S → IsSquareFree S) ∧
      (∀ F : List α, F <:+: S → IsSyncString ε S → IsSyncString ε F) ∧
      (∀ F : List α, F <:+: S → IsSquareFree S → IsSquareFree F) := by sorry

end TernarySync.Alphabet
