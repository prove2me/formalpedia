-- Prove2me | Theorems.Thm_RGGThreshold_lemma_2_5
-- name    : RGGThreshold.lemma_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:59:57.712071+00:00
-- url     : https://prove2.me/theorems/4dc1c270-ee07-4dc1-84e0-4fc369e91e68
-- title:
--   Lemma 2.5 — the vector event $\mathcal F$ has probability $1-o(1)$
-- statement:
--   Let $v_1,\dots,v_n$ be obtained from the Gram–Schmidt procedure applied to independent uniform points $x_1,\dots,x_n$ of $\mathbb S^{d-1}$, and assume $n\le d/2$. Then
--
--   $$
--   \mathbb P\big[(v_1,\dots,v_n)\ \text{satisfy}\ \mathcal F\big]=1-o(1)\qquad(n\to\infty).
--   $$
--
--   Intersecting with $\mathcal F$ therefore changes the total variation distance by a vanishing amount.
--
--   **Formalization Note** $1-o(1)$ means: for every $\eta>0$ there is $N$ such that the probability is at least $1-\eta$ for all $n\ge N$ and every $d\ge2n$.
--
--   Differences from the source:
--
--   - reading: 1 − o(1) as n → ∞ → ∀ η > 0, ∃ N, ∀ n ≥ N, ∀ d ≥ 2n: probability ≥ 1 − η; reason: uniform over d, equivalent to the statement for every sequence d(n) ≥ 2n
--   - encoding: vertices and coordinates 1, …, n → Fin n, numbered from 0; reason: index shift only; each statement shifts s accordingly
-- source:
--   Hunter–Milojević–Sudakov, Distinguishability Threshold for Random Geometric Graphs, arXiv:2607.22480 (held version, sha256 1a398ef9…), Lemma 2.5, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_RGGThreshold_eventF

open MeasureTheory

namespace RGGThreshold

/-- **Lemma 2.5** (Hunter–Milojević–Sudakov, *Distinguishability Threshold for Random Geometric Graphs*, arXiv:2607.22480, held version, sha256 1a398ef9…, Lemma 2.5, p.9 (PDF p.11)). Let `v_1, …, v_n` be obtained from the
Gram–Schmidt procedure applied to `x_1, …, x_n` (independent, uniform on `S^{d-1}`), and assume
that `n ≤ d/2`. Then `P[(v_1, …, v_n) satisfy 𝓕] = 1 - o(1)` as `n → ∞`.

**Formalization Note** `1 - o(1)` as `n → ∞` is: for every `η > 0` there is `N` such that for all
`n ≥ N` and every `d ≥ 2n` the probability is at least `1 - η`. -/
theorem lemma_2_5 :
    ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ d : ℕ, 2 * n ≤ d →
    1 - η ≤ (RGGDetect.prior n d).real (eventF n d) := by sorry

end RGGThreshold
