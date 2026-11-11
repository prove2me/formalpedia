-- Prove2me | Theorems.Thm_RandProdExp_TwoSided_corollary_8_28
-- name    : RandProdExp.TwoSided.corollary_8_28
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:18:43.392195+00:00
-- url     : https://prove2.me/theorems/954d86bf-2116-4dcb-9d34-24c80e22e516
-- title:
--   Corollary 8.28 — $|W_p(\Delta)|\le16^p(4p)^{6\Delta}$
-- statement:
--   Let $1\le k\le n$, an integer $p\ge1$ and a deficiency $\Delta\ge0$. The number of equivalence classes of even non-left-backtracking closed walks from Definition 8.4 (length $4p+1$, left letters in $[n]$ at even positions, right letters in $[k]$ at odd positions) with deficiency $\Delta$ satisfies
--   $$|W_p(\Delta)|\le16^p\,(4p)^{6\Delta}.$$
--   It specializes Proposition 8.25 to the walks produced by the trace expansion.
--
--   Differences from the source:
--   - encoding: the setup of §8 (k_j ∈ [n]) and the letters {L} × [n], {R} × [k_j] of Definition 8.4 → hypotheses 1 ≤ k ≤ n; alphabet Fin n ⊕ Fin k; reason: standing assumptions of §8 (p. 55)
--   - encoding: 'the number of equivalence classes is at most X' → the set of classes is finite and its ncard is ≤ X; reason: ncard is 0 on infinite sets, so finiteness is stated explicitly
--   - encoding: the equivalence class (Definition 8.14) of a walk among the walks of Definition 8.4 → the set of all words over Fin n ⊕ Fin k equivalent to it (walkClasses); reason: two walks are equivalent iff their full classes coincide, so the number of classes is the same
-- source:
--   Chattopadhyay, Ringach, Spooner, Product Expansion of Random Codes via Analytic Techniques, STOC 2027 submission (manuscript sha256 9e4ac2d1…), p. 61, Corollary 8.28

import Mathlib
import Definitions.Def_RandProdExp_TwoSided_Words

namespace RandProdExp.TwoSided

/-- **Corollary 8.28** (p. 61). For an integer `p ≥ 1` and deficiency `Δ ≥ 0`, the number of
equivalence classes of even non-left-backtracking closed walks from Definition 8.4 (left letters in
`[n]`, right letters in `[k]`, `k ∈ [n]`) is at most `|W_p(Δ)| ≤ 16^p (4p)^{6Δ}`. -/
theorem corollary_8_28 (n k p Δ : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (hp : 1 ≤ p) :
    (walkClasses n k p Δ).Finite ∧
      (walkClasses n k p Δ).ncard ≤ 16 ^ p * (4 * p) ^ (6 * Δ) := by sorry

end RandProdExp.TwoSided
