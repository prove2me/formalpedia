-- Prove2me | Theorems.Thm_TIESharp_lemma_4_4
-- name    : TIESharp.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:37:02.991676+00:00
-- url     : https://prove2.me/theorems/b12ebf32-4911-4713-ba02-71534410185f
-- title:
--   Lemma 4.4 — vanishing of high-order interactions ($s\ge n\ge2$)
-- statement:
--   Let $s\ge n\ge2$ and consider the open orthant of coordinates $t_{ij}>0$, $i\in[n]$, $j\in[s]$. Suppose the measurable functions $W_1,\dots,W_n$ have weak partial derivatives $\partial_{ij}W_i$, and that for a finite constant $C\ge0$, almost everywhere,
--   $$|W_i(t)|\le C\,t_{ij},\qquad|\partial_{ij}W_i(t)|\le C\quad\text{for all }i,j,\qquad \sum_i\partial_{ij}W_i(t)=0\quad\text{for all }j.$$
--   Then $W_i=0$ almost everywhere for every $i$.
--
--   Applied to the alternating sums of potentials over job subsets, the lemma shows that interactions among $n$ or more jobs vanish, so each job's assignment probability depends on at most $n-2$ other jobs.
--
--   Differences from the source:
--   - encoding: weak partial derivatives ∂_ij W_i → functions w i j with IsWeakPartial (W i) (w i j) i j on the open orthant; reason: the derivative of W_i in its own-row entry (i, j), the only ones the statement uses
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), Lemma 4.4, p.19

import Mathlib
import Definitions.Def_TIESharp_IsWeakPartial

set_option autoImplicit false

open MeasureTheory

namespace TIESharp

/-- **Lemma 4.4 (Vanishing of high-order interactions)** (Li, *Sharp Bounds for
Truthful-in-Expectation Scheduling*, arXiv:2611.05134, Lemma 4.4, p.19). Let `s ≥ n ≥ 2`, with
coordinates `t_ij > 0` for `i ∈ [n]`, `j ∈ [s]`. Suppose the measurable functions `W_1, …, W_n` on
the open orthant `(0, ∞)^{n×s}` have weak partial derivatives `∂_ij W_i`. For a finite constant
`C ≥ 0`, assume `|W_i(t)| ≤ C t_ij` and `|∂_ij W_i(t)| ≤ C` for all `i, j`, and
`Σ_i ∂_ij W_i(t) = 0` for all `j`, almost everywhere. Then `W_i = 0` almost everywhere for every `i`.

**Formalization Note.** `w i j` is the weak partial derivative `∂_ij W_i` of `W_i` in its own-row
entry `(i, j)` (`IsWeakPartial`, test functions supported in the open orthant); only these
derivatives appear on the page. "Almost everywhere" is with respect to Lebesgue measure restricted
to the open orthant. -/
theorem lemma_4_4 (n s : ℕ) (hn : 2 ≤ n) (hns : n ≤ s)
    (W : Fin n → (Fin n → Fin s → ℝ) → ℝ) (w : Fin n → Fin s → (Fin n → Fin s → ℝ) → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hW : ∀ i, Measurable (W i))
    (hw : ∀ i j, IsWeakPartial (W i) (w i j) i j)
    (hbd : ∀ᵐ t ∂(volume.restrict {t : Fin n → Fin s → ℝ | ∀ i j, 0 < t i j}),
      ∀ i j, |W i t| ≤ C * t i j ∧ |w i j t| ≤ C)
    (hsum : ∀ᵐ t ∂(volume.restrict {t : Fin n → Fin s → ℝ | ∀ i j, 0 < t i j}),
      ∀ j, ∑ i, w i j t = 0) :
    ∀ i, W i =ᵐ[volume.restrict {t : Fin n → Fin s → ℝ | ∀ i j, 0 < t i j}] 0 := by sorry

end TIESharp
