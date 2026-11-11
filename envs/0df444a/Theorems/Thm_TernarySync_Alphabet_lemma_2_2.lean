-- Prove2me | Theorems.Thm_TernarySync_Alphabet_lemma_2_2
-- name    : TernarySync.Alphabet.lemma_2_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:52:39.514639+00:00
-- url     : https://prove2.me/theorems/6c5cff14-e565-491e-af7c-9144d8627e7c
-- title:
--   Lemma 2.2 — an equal-length LCS deficit $\eta$ gives $\varepsilon$-synchronization whenever $1-\varepsilon < \eta/(2+\eta)$
-- statement:
--   Let $0 < \eta < 1$ and let $S$ be a word over any alphabet. Suppose that for every length $\ell \ge 1$ and every available start $t$ (both $S[t, t+\ell)$ and $S[t+\ell, t+2\ell)$ lie inside $S$)
--
--   $$\mathrm{LCS}\big(S[t,t+\ell),\, S[t+\ell,t+2\ell)\big) \le (1-\eta)\,\ell. \tag{4}$$
--
--   Then $S$ is an $\varepsilon$-synchronization string for every $0 \le \varepsilon < 1$ with $1 - \varepsilon < \eta/(2+\eta)$. In particular $S$ has synchronization gap $\eta/3$, i.e. it is a $(1-\eta/3)$-synchronization string.
--
--   This lemma passes from adjacent intervals of *equal* length, which the probabilistic construction controls, to arbitrary adjacent intervals as Definition 1.1 requires, losing a factor in the gap.
--
--   **Formalization Note.** Indices are 0-based: an available start for length $\ell$ is a $t \ge 0$ with $t + 2\ell \le |S|$, and $S[t,t+\ell)$ is `factor S t (t+ℓ)`.
--
--   Differences from the source:
--   - encoding: 1-based half-open factors $S[i,j)$ with $1 \le i \le j \le n+1$ → 0-based `factor S i j` = positions $i,\dots,j-1$, so the ranges shift by one (e.g. $k \le n+1$ becomes $k \le n$); reason: index shift only; the same factors and the same instances
--   - encoding: ε-synchronization string (Definition 1.1, 0 ≤ ε < 1) whenever 1 − ε < η/(2 + η) → ∀ ε, 0 ≤ ε → ε < 1 → 1 − ε < η/(2 + η) → IsSyncString ε S; reason: the range of Definition 1.1 written as binders
--   - encoding: synchronization gap η/3 → IsSyncString (1 − η/3) S; reason: the gap is 1 − ε by Definition 1.1
-- source:
--   Xu, Fu, Qiao, Tao, Synchronization Strings over a Ternary Alphabet, STOC 2027 submission (manuscript sha256 1b74ae6d…), p. 13 (PDF 14), Lemma 2.2

import Mathlib
import Definitions.Def_TernarySync_Alphabet_SyncString

set_option autoImplicit false

namespace TernarySync.Alphabet

/-- Lemma 2.2 (p. 13): let `0 < η < 1` and suppose `LCS(S[t, t + ℓ), S[t + ℓ, t + 2ℓ)) ≤ (1 − η)ℓ`
for every length `ℓ ≥ 1` and every available start `t` (0-based: `t + 2ℓ ≤ |S|`). Then `S` is an
`ε`-synchronization string for every `0 ≤ ε < 1` with `1 − ε < η/(2 + η)`; in particular it has
synchronization gap `η/3`, i.e. it is a `(1 − η/3)`-synchronization string. -/
theorem lemma_2_2 {α : Type*} (S : List α) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1)
    (h4 : ∀ t ℓ : ℕ, 1 ≤ ℓ → t + 2 * ℓ ≤ S.length →
      (lcs (factor S t (t + ℓ)) (factor S (t + ℓ) (t + 2 * ℓ)) : ℝ) ≤ (1 - η) * (ℓ : ℝ)) :
    (∀ ε : ℝ, 0 ≤ ε → ε < 1 → 1 - ε < η / (2 + η) → IsSyncString ε S) ∧
      IsSyncString (1 - η / 3) S := by sorry

end TernarySync.Alphabet
