-- Prove2me | Theorems.Thm_SchedComplexity_Tardiness_knapsack_wt_encoding_reduction
-- name    : SchedComplexity.Tardiness.knapsack_wt_encoding_reduction
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-27T06:41:21.789322+00:00
-- url     : https://prove2.me/theorems/5cc7e593-3e3e-4061-9424-a0d4a44ea2c1
-- title:
--   Theorem 4(d) — Polynomial-Time Multiplicity-Encoding Reduction from KNAPSACK to $n|1||\sum w_j T_j$
-- statement:
--   There exists a polynomial-time computable function $f$ on $\mathrm{BSym}$ strings that maps binary-coded KNAPSACK instances $\mathrm{encNats}(b :: a)$ with $0 < b < A$ to multiplicity-encoded instances in $\mathrm{wtLangMult}$ with parameter $\tau = 2t' + A + 1$, and resolves boundary instances $b \ge A$.
-- source:
--   Brucker, Lenstra & Rinnooy Kan 1975, Complexity of Machine Scheduling Problems, Report BW 43/75, pp. 20–21, 23, Theorem 4(d) and Remark

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Set.Card
import Mathlib.Data.List.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic
import Definitions.Def_SchedComplexity_Tardiness_Knapsack
import Definitions.Def_SchedComplexity_Tardiness_MultLang
import Definitions.Def_SchedComplexity_Tardiness_Construction

namespace SchedComplexity.Tardiness

open CookPvsNP ProjSchedTW.Complexity

/-- Polynomial-time multiplicity-encoding reduction for Theorem 4(d) (Brucker, Lenstra &
Rinnooy Kan 1975, pp. 20–21, Remark p. 23): there is a polynomial-time computable function `f` on
`BSym` strings that maps binary-coded KNAPSACK instances `encNats (b :: List.ofFn a)` with
`0 < b < bigA a` to multiplicity-encoded instances in `wtLangMult` with parameter
`τ = 2 * tPrime a b + bigA a + 1`, and handles boundary instances `b ≥ bigA a`. -/
theorem knapsack_wt_encoding_reduction :
    ∃ f : List BSym → List BSym, PolyTimeComputable f ∧
      ∀ x : List BSym,
        ((∃ (t : ℕ) (a : Fin t → ℕ) (b : ℕ),
            (∀ j, 0 < a j) ∧ 0 < b ∧ b < bigA a ∧
            HasScheduleLE (wtP a b (2 * tPrime a b + bigA a + 1))
              (wtW a b (2 * tPrime a b + bigA a + 1))
              (wtD a b (2 * tPrime a b + bigA a + 1))
              (yThr a b (2 * tPrime a b + bigA a + 1)) ∧
            x = encNats (b :: List.ofFn a)) ∨
          (∃ (t : ℕ) (a : Fin t → ℕ) (b : ℕ),
            (∀ j, 0 < a j) ∧ 0 < b ∧ b = bigA a ∧ x = encNats (b :: List.ofFn a))) ↔
          f x ∈ wtLangMult := by sorry

end SchedComplexity.Tardiness
