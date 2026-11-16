-- Prove2me | Theorems.Thm_ShiAuthentication_BA_Supplement_corollary_5_3
-- name    : ShiAuthentication.BA.Supplement.corollary_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:28:28.44388+00:00
-- url     : https://prove2.me/theorems/18d02fd5-c816-484c-89af-9a464889424d
-- title:
--   Corollary 5.3 — subquadratic broadcast setups
-- statement:
--   For $n\ge3$, $1\le t<n$ and every designated sender $S$:
--
--   1. $A_{BB}(n,t)=O\big(n(2t-n)_+ + n^{3/2}\sqrt{\ln n}\big)$, where $(x)_+=\max\{x,0\}$;
--   2. for $t\le n/2$, $A_{BB}(n,t)=O\big(n^{3/2}\sqrt{\ln n}\big)$;
--   3. $A_{BB}(n,t)=o(n^2)$ whenever $t=n/2+o(n)$.
--
--   The constants in 1 and 2 are absolute (the same for all $n,t,S$). Item 3 means: for every sequence $t=\tau(n)$ with $(\tau(n)-n/2)/n\to0$ and every $\varepsilon>0$, for all sufficiently large $n$ and every sender,
--   $$A_{BB}(n,\tau(n))\le\varepsilon n^2 .$$
--
--   Unlike agreement, which needs a complete PKI at $n=2t+1$, broadcast admits subquadratic setups around the honest-majority threshold.
--
--   Differences from the source:
--   - encoding: A_BB(n, t) → ABB t S, stated for every designated sender S; reason: Definition 3.3 minimizes over setups for broadcast from a designated sender; the bound is claimed for every sender
--   - encoding: values of A_T(n, t) in ℕ ∪ {+∞} → ℕ∞, compared with real bounds after the cast ℕ∞ → ℝ≥0∞ and ENNReal.ofReal; reason: +∞ is the infimum of the empty family (Definition 3.3); an upper bound in ℝ≥0∞ also asserts finiteness
--   - encoding: O(·) bounds → ∃ C > 0 before ∀ n t S; reason: the O ranges over n and t; uniform constants
--   - encoding: t ≤ n/2 → 2 * t ≤ n; reason: equivalent for integers
--   - encoding: A_BB(n, t) = o(n²) whenever t = n/2 + o(n) → ∀ τ : ℕ → ℕ with (τ n − n/2)/n → 0, ∀ ε > 0, eventually ∀ S, A_BB(n, τ n) ≤ ε n²; reason: the standard meaning of the two little-o symbols; every admissible sequence is covered, and n ≥ 3, 1 ≤ τ n < n hold eventually
-- source:
--   Kecheng Shi, STOC 2027 submission #203 (October 2026), Corollary 5.3, p. 26

import Definitions.Def_ShiAuthentication_BA_Supplement_Complexity

set_option autoImplicit false

open Filter Topology
open scoped ENNReal

namespace ShiAuthentication.BA.Supplement

/-- **Corollary 5.3**, p. 26. With absolute constants uniform over all `n ≥ 3`, `1 ≤ t < n` and
all senders `S`:
(1) `A_BB(n, t) = O(n(2t − n)₊ + n^{3/2} √(ln n))`, where `(x)₊ = max{x, 0}`;
(2) for `t ≤ n/2`, `A_BB(n, t) = O(n^{3/2} √(ln n))`;
(3) `A_BB(n, t) = o(n²)` whenever `t = n/2 + o(n)`: for every `τ : ℕ → ℕ` with
`(τ(n) − n/2)/n → 0` and every `ε > 0`, eventually `A_BB(n, τ(n)) ≤ ε n²` for every sender. -/
theorem corollary_5_3 :
    (∃ C : ℝ, 0 < C ∧ ∀ (n t : ℕ) (S : Fin n), 3 ≤ n → 1 ≤ t → t < n →
      (ABB t S : ℝ≥0∞) ≤ ENNReal.ofReal
        (C * ((n : ℝ) * max (2 * (t : ℝ) - n) 0 +
          (n : ℝ) ^ ((3 : ℝ) / 2) * Real.sqrt (Real.log n)))) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (n t : ℕ) (S : Fin n), 3 ≤ n → 1 ≤ t → t < n → 2 * t ≤ n →
      (ABB t S : ℝ≥0∞) ≤ ENNReal.ofReal
        (C * ((n : ℝ) ^ ((3 : ℝ) / 2) * Real.sqrt (Real.log n)))) ∧
    (∀ τ : ℕ → ℕ, Tendsto (fun n : ℕ => ((τ n : ℝ) - (n : ℝ) / 2) / n) atTop (𝓝 0) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ S : Fin n,
        (ABB (τ n) S : ℝ≥0∞) ≤ ENNReal.ofReal (ε * (n : ℝ) ^ 2)) := by sorry

end ShiAuthentication.BA.Supplement
