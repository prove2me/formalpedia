-- Prove2me | Theorems.Thm_PvsNP_spatialBidiagonal_firstCell
-- name    : PvsNP.spatialBidiagonal_firstCell
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T17:20:44.034696+00:00
-- url     : https://prove2.me/theorems/e17fe1ac-b736-446f-bfdf-e08c8d155662
-- title:
--   Exact finite formula for a position-dependent bidiagonal tape update
-- statement:
--   Start with a finite list of semiring elements on a one-sided tape, extending the tape by zeros. Fix a Boolean stay flag and pull flag at every position. In one round, cell $i$ adds its previous value if its stay flag is enabled and the previous value of cell $i+1$ if its pull flag is enabled. After $t$ rounds, the contribution from initial cell $d$ to cell zero vanishes if $d>t$ or some pull flag before $d$ is disabled. Otherwise its coefficient is the number of weak compositions of $t-d$ over the positions from $0$ through $d$ whose stay flags are enabled. With no staying steps the coefficient is one, and with staying steps but no enabled positions it is zero. The coefficient multiplies the original value at offset $d$, and the sum only needs offsets in the original list.
-- source:
--   C. de Boor, Divided Differences, Surveys in Approximation Theory 1 (2005), 46–69, §4, pp. 54–55, Proposition 25 and Example 7 (bidiagonal path expansion), https://pages.cs.wisc.edu/~deboor/sat/papers/2/2.pdf. The submitted identity specializes to Boolean stay flags, adds possibly disabled pull edges, and works directly over semirings on zero-extended lists.

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

open scoped BigOperators

theorem PvsNP.spatialBidiagonal_firstCell {K : Type} [Semiring K]
    (stay pull : ℕ → Bool) (data : List K) (t : ℕ) :
    let step (v : ℕ → K) (i : ℕ) : K :=
      ((stay i).toNat : K) * v i + ((pull i).toNat : K) * v (i + 1)
    let w (d : ℕ) : ℕ := ∑ j ∈ Finset.range (d + 1), (stay j).toNat
    let paths (d : ℕ) : ℕ :=
      if d ≤ t ∧ (∀ j < d, pull j = true) then
        if t = d then 1 else if w d = 0 then 0 else (t - d + w d - 1).choose (t - d)
      else 0
    (step^[t] (fun i => data[i]?.getD 0)) 0 =
      ∑ d ∈ Finset.range data.length, (paths d : K) * data[d]?.getD 0 := by sorry
