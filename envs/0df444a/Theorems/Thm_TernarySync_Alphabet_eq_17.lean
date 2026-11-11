-- Prove2me | Theorems.Thm_TernarySync_Alphabet_eq_17
-- name    : TernarySync.Alphabet.eq_17
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:54:46.721201+00:00
-- url     : https://prove2.me/theorems/0ff067a9-dc3a-4343-8745-cab7ed84737b
-- title:
--   Eq. (17) — some choice vector gives $\mathrm{LCS}(X,Y) \le (1-\eta)\ell$ for every adjacent equal-length pair
-- statement:
--   Let $\eta = 1/1000$ and let $T$ be a finite square-free outer word of length $N$ over $\{0,1,2\}$. There is a choice vector $R \in \{0,1\}^N$ such that the output $W = W(T,R)$ satisfies
--
--   $$\mathrm{LCS}\big(W[t,t+\ell),\, W[t+\ell,t+2\ell)\big) \le (1-\eta)\,\ell \tag{17}$$
--
--   for every adjacent equal-length pair: every length $\ell \ge 1$ and every available start $t$.
--
--   Long pairs ($\ell > 1000$) come from the local lemma applied to the events $E_{t,\ell}$; short pairs ($\ell \le 1000$) from square-freeness: two adjacent equal words would form a square, so $\mathrm{LCS} \le \ell - 1 \le (1-\eta)\ell$. Via Lemma 2.2, (17) gives the synchronization property of the length-$n$ prefix of $W$.
--
--   **Formalization Note.** Indices are 0-based; $t$ is available when $t + 2\ell \le 18N$.
--
--   Differences from the source:
--   - encoding: 1-based half-open factors $S[i,j)$ with $1 \le i \le j \le n+1$ → 0-based `factor S i j` = positions $i,\dots,j-1$, so the ranges shift by one (e.g. $k \le n+1$ becomes $k \le n$); reason: index shift only; the same factors and the same instances
--   - reading: (17) for this same output, i.e. the output selected by the local lemma → there exists R : Fin |T| → Fin 2 with the bound for every ℓ ≥ 1 and every available t; reason: the selected output is some choice vector; existence is what the equation asserts about it
--   - encoding: T a fixed finite square-free outer word (§4) → hypothesis IsSquareFree T; reason: the section's standing assumption written as a binder
-- source:
--   Xu, Fu, Qiao, Tao, Synchronization Strings over a Ternary Alphabet, STOC 2027 submission (manuscript sha256 1b74ae6d…), p. 17 (PDF 18), §4, Eq. (17)

import Mathlib
import Definitions.Def_TernarySync_Alphabet_RandomSource

set_option autoImplicit false

namespace TernarySync.Alphabet

/-- Equation (17) (p. 17): for every finite square-free outer word `T` there is a choice vector
`R` such that `W = W(T, R)` satisfies `LCS(X, Y) ≤ (1 − η)ℓ`, `η = 1/1000`, for every adjacent
equal-length pair `X = W[t, t + ℓ)`, `Y = W[t + ℓ, t + 2ℓ)`: every length `ℓ ≥ 1` and every
available start `t` (0-based, `t + 2ℓ ≤ 18 |T|`). -/
theorem eq_17 (T : List (Fin 3)) (hT : IsSquareFree T) :
    ∃ R : Fin T.length → Fin 2, ∀ t ℓ : ℕ, 1 ≤ ℓ → t + 2 * ℓ ≤ 18 * T.length →
      (lcs (blockX T R t ℓ) (blockY T R t ℓ) : ℝ) ≤ (1 - (1 : ℝ) / 1000) * (ℓ : ℝ) := by sorry

end TernarySync.Alphabet
