-- Prove2me | Theorems.Thm_RandDelMatroid_Indep_random_delete_independent
-- name    : RandDelMatroid.Indep.random_delete_independent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T18:29:18.221821+00:00
-- url     : https://prove2.me/theorems/0e7fe62a-e3aa-4b05-b257-6a9f63f0aa6f
-- title:
--   Theorem 1 — random deletion leaves an independent set with probability ≥ 1 − 1/m⁵
-- statement:
--   Let $M=(E,\mathcal I)$ be a regular matroid with $m=|E|\ge2$ elements and minimum circuit size $g$. Run Algorithm 1: keep every element of $E$ independently with probability $m^{-40/g}$ (delete it with probability $1-m^{-40/g}$), and let $R$ be the set of kept elements. Then
--
--   $$\Pr[R\in\mathcal I]\ \ge\ 1-\frac1{m^5}.$$
--
--   This is the main result of the paper: one round of independent random deletion at rate $1-m^{-40/g}$ destroys every circuit of a regular matroid with high probability. Theorem 2 and the $m^{O(\alpha)}$ bound on the number of $\alpha$-approximate minimum circuits are derived from it.
--
--   **Formalization Note** The probability is the exact finite sum of the product law (`alg1Prob`). Regularity is representability over every field (Definition 8).
--
--   Differences from the source:
--   - encoding: regular = representable over every field → representable over every field F : Type; reason: Lean quantifies over fields in the base universe; this is a weaker hypothesis on M, so the statement covers every regular matroid
--   - encoding: matroid M = (E, I) with E a finite ground set (Definition 1) → Mathlib Matroid on an element type with finite ground set M.E; reason: Definition 1's matroids are finite; any finite matroid is a Lean Matroid with finite ground set
--   - encoding: g = min{|C| : C a circuit of M} → hypothesis IsMinCircuitSize M g (some circuit has g elements, every circuit has at least g); reason: the minimum is defined only when M has a circuit; the hypothesis excludes only that undefined case
-- source:
--   Karthekeyan Chandrasekaran, Chandra Chekuri, Weihao Zhu, STOC 2027 submission #536 (October 2026), p. 3, Theorem 1 (Algorithm 1, p. 3)

import Mathlib
import Definitions.Def_RandDelMatroid_Indep_Regular
import Definitions.Def_RandDelMatroid_Indep_MinCircuitSize
import Definitions.Def_RandDelMatroid_Indep_RandomDelete

set_option autoImplicit false

open scoped NNReal

namespace RandDelMatroid.Indep

/-- Theorem 1 (p. 3). Let `M = (E, I)` be a regular matroid with `m ≥ 2` elements and minimum
circuit size `g`. Algorithm 1 (keep each element independently with probability `m^(-40/g)`)
returns a set `R` that is independent with probability at least `1 - 1/m^5`. -/
theorem random_delete_independent {α : Type} (M : Matroid α) [M.Finite] (hreg : IsRegular M)
    (hm : 2 ≤ M.E.ncard) (g : ℕ) (hg : IsMinCircuitSize M g) :
    1 - 1 / (M.E.ncard : ℝ) ^ 5 ≤ alg1Prob M g {R | M.Indep R} := by sorry

end RandDelMatroid.Indep
