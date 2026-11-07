-- Prove2me | Theorems.Thm_PredAdvice_display_14
-- name    : PredAdvice.display_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:34:07.783199+00:00
-- url     : https://prove2.me/theorems/1b96e5d7-88fb-47fa-9ee1-67ad7d3ad0c2
-- title:
--   Proof of Theorem 1.1, eq. (14) — $D=\max\{2,\lfloor R^{1/3}\rfloor\}$, $L=\lceil 3\log D\rceil$
-- statement:
--   There is an absolute constant $C>0$ such that for every $n\ge2$, with $R=RS(n)$, $D=\max\{2,\lfloor R^{1/3}\rfloor\}$ and $L=\lceil3\log_2D\rceil$:
--
--   1. $2\le D\le n$ and $L\ge1$;
--   2. $2^L\ge D^3$ and $D^2/2^L\le1/D$;
--   3. $C^{-1}\le D^3/R\le C$ and $\log_2D\le L\le C\log_2D$, hence $LD^2/R\le C\log_2D/D$;
--   4. (eq. (14))
--   $$
--   \frac{\log D}{D}+\frac1D+\frac{D^2}{2^L}+\frac{LD^2}{R}\le C\,\frac{1+\log D}{D}\qquad\text{and}\qquad \frac{1+\log D}{D}\le C\,\frac{1+\log R}{R^{1/3}};
--   $$
--   5. $n\le n^2/D\le C\,n^2/R^{1/3}$.
--
--   These are the numerical facts that turn the tree-cover bound (13) into the space bound of Theorem 1.1.
--
--   Differences from the source:
--   - encoding: Θ(·) and O(·) of the proof → one absolute constant C for all n ≥ 2; reason: standard reading
--   - encoding: (14) for m_T with the factor n² → the bracket of (13) bounded without the common factor n²; reason: the same inequality divided by n²
-- source:
--   Kopelowitz, Korin, Roditty, Using Small Advice to Compress the Predecessor Matrix, STOC 2027 submission (manuscript sha256 0ae8a68d…), proof of Theorem 1.1, eq. (14), p.24, and p.25

import Mathlib
import Definitions.Def_PredAdvice_RS

set_option autoImplicit false

namespace PredAdvice

/-- **The parameter choice and eq. (14)** (proof of Theorem 1.1, Kopelowitz, Korin, Roditty, *Using Small Advice to Compress the Predecessor Matrix*, STOC 2027 submission (manuscript sha256 0ae8a68d…), pp.24–25). For `n ≥ 2` set
`R := RS(n)`, `D := max{2, ⌊R^{1/3}⌋}` and `L := ⌈3 log D⌉`. Then `2 ≤ D ≤ n`, `L ≥ 1`,
`2^L ≥ D³`, `D²/2^L ≤ 1/D`, `D³ = Θ(R)`, `L = Θ(log D)`, `L D²/R = O(log D/D)`,

`log D/D + 1/D + D²/2^L + L D²/R = O((1 + log D)/D) = O((1 + log R)/R^{1/3})` (eq. (14)),

and `n ≤ n²/D = O(n²/R^{1/3})`.

**Formalization Note** One absolute constant `C > 0` serves every `Θ` and `O`, for all `n ≥ 2`. The
bracket of eq. (14) is the bracket of (13), and multiplying by `n²` gives the printed (14).
`D ≤ n` is used without proof in the paper ("Since D ≤ n"); it is a clause here. -/
theorem display_14 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      let R := RS n
      let D : ℕ := max 2 ⌊R ^ (1 / 3 : ℝ)⌋₊
      let L : ℕ := ⌈3 * Real.logb 2 D⌉₊
      2 ≤ D ∧ D ≤ n ∧ 1 ≤ L ∧ (D : ℝ) ^ 3 ≤ 2 ^ L ∧ (D : ℝ) ^ 2 / 2 ^ L ≤ 1 / (D : ℝ) ∧
      C⁻¹ ≤ (D : ℝ) ^ 3 / R ∧ (D : ℝ) ^ 3 / R ≤ C ∧
      (L : ℝ) ≤ C * Real.logb 2 D ∧ Real.logb 2 D ≤ L ∧
      (L : ℝ) * (D : ℝ) ^ 2 / R ≤ C * (Real.logb 2 D / D) ∧
      Real.logb 2 D / D + 1 / (D : ℝ) + (D : ℝ) ^ 2 / 2 ^ L + (L : ℝ) * (D : ℝ) ^ 2 / R ≤
        C * ((1 + Real.logb 2 D) / D) ∧
      (1 + Real.logb 2 D) / D ≤ C * ((1 + Real.logb 2 R) / R ^ (1 / 3 : ℝ)) ∧
      (n : ℝ) ≤ (n : ℝ) ^ 2 / D ∧ (n : ℝ) ^ 2 / D ≤ C * ((n : ℝ) ^ 2 / R ^ (1 / 3 : ℝ)) := by sorry

end PredAdvice
