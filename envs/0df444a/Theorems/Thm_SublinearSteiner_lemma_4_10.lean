-- Prove2me | Theorems.Thm_SublinearSteiner_lemma_4_10
-- name    : SublinearSteiner.lemma_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:41:03.793046+00:00
-- url     : https://prove2.me/theorems/9309890b-313a-4f1e-b4f2-e9f017f3ae1a
-- title:
--   Lemma 4.10 — reusable sample
-- statement:
--   Let $R_1,\dots,R_{N_r}$ be fixed rows in a universe of size $g$, let $t\ge1$ and $0<\beta<1/4$. The procedure (4.17), which knows $t$ but not $g$, uses
--   $$N_s=O\bigl(t\log(t/\beta)\log((N_r+1)t/\beta)\bigr)$$
--   independent uniform samples of the universe and $O(N_rN_s)$ membership tests, and it selects at most $t$ rows such that, except with probability $\beta$, every selected row contains at least $g/t$ elements outside the previously selected rows, and in the end every row contains at most $4g/t$ elements outside the selected rows.
--
--   One pool of samples thus serves all rows, without a fresh sample for each test.
--
--   Differences from the source:
--   - reading: a procedure → the explicit rule (4.17) with b = C_b log(t/β) and N_s = ⌈C t log(t/β) log((N_r+1)t/β)⌉, for universal C, C_b; reason: an abstract procedure could read the rows whole; these are the proof’s choices
--   - encoding: O(N_r N_s) membership tests → at most N_r N_s tests on every run; reason: the count of the rule is deterministic
--   - encoding: a universe of size g → a nonempty finite type Uni, g = its cardinality; reason: uniform samples of the universe need g ≥ 1; for an empty universe with N_s ≥ 1 the statement is trivially true
-- source:
--   Mahabadi, Roghani, Tarnawski, Vakilian, Tight Bounds for Sublinear Metric Steiner Tree, STOC 2027 submission (manuscript sha256 ae133037…), Lemma 4.10, (4.17), p.26

import Mathlib
import Definitions.Def_SublinearSteiner_ReusableSample

open scoped Classical

namespace SublinearSteiner

/-- Mahabadi, Roghani, Tarnawski, Vakilian, *Tight Bounds for Sublinear Metric Steiner Tree*, STOC 2027 submission (manuscript sha256 ae133037…), Lemma 4.10 (Reusable sample), p.26. Let `R_1, …, R_{N_r}` be fixed rows in a universe of size `g`, let `t ≥ 1`, and let
`0 < β < 1/4`. A procedure that knows `t` but not `g` uses `N_s = O(t log(t/β) log((N_r + 1)t/β))` independent uniform samples of the universe and
`O(N_r N_s)` membership tests, and selects at most `t` rows such that, except with probability `β`, every selected row contains at least
`g/t` elements outside the previously selected rows, and in the end every row contains at most `4g/t` elements outside the selected rows.

**Formalization Note.**
* The procedure is the explicit rule (4.17). An abstract "there is a procedure" would be satisfied by one reading the rows whole.
* `C` and `C_b` are universal, chosen first. `b = C_b log(t/β)` and `N_s = ⌈C t log(t/β) log((N_r + 1)t/β)⌉` are functions of `t, β, N_r` only.
* "At most `t` rows" and "`O(N_r N_s)` tests" hold on every run, the latter with constant `1`.
* The law: `X` is uniform on `N_s`-tuples of the universe and `u` is uniform on `[0, 1]^{N_r}`, independently. -/
theorem lemma_4_10 :
    ∃ C Cb : ℝ, 0 < C ∧ 0 < Cb ∧ ∀ (Uni : Type) [Fintype Uni] [Nonempty Uni] (Nr t : ℕ) (β : ℝ),
      1 ≤ t → 0 < β → β < 1 / 4 → ∀ R : Fin Nr → Finset Uni,
      let b : ℝ := Cb * Real.log ((t : ℝ) / β)
      let Ns : ℕ := ⌈C * t * Real.log ((t : ℝ) / β) * Real.log (((Nr : ℝ) + 1) * t / β)⌉₊
      (∀ (X : Fin Ns → Uni) (u : Fin Nr → ℝ),
        (sampleRun R X u t b).selected.length ≤ t ∧ (sampleRun R X u t b).tests ≤ Nr * Ns) ∧
      ((Fintype.card (Fin Ns → Uni) : ℝ)⁻¹ * ∑ X : Fin Ns → Uni,
          ((MeasureTheory.volume : MeasureTheory.Measure (Fin Nr → ℝ))
            {u | (∀ j, u j ∈ Set.Icc (0 : ℝ) 1) ∧
              ¬ SelectionGood R (Fintype.card Uni) t (sampleRun R X u t b).selected}).toReal) ≤ β := by sorry

end SublinearSteiner
