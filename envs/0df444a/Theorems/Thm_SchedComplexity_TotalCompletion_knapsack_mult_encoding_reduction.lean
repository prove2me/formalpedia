-- Prove2me | Theorems.Thm_SchedComplexity_TotalCompletion_knapsack_mult_encoding_reduction
-- name    : SchedComplexity.TotalCompletion.knapsack_mult_encoding_reduction
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-27T06:40:58.452027+00:00
-- url     : https://prove2.me/theorems/fb79e27b-c76c-4ee6-be0e-c59cc3a6aa1b
-- title:
--   Theorem 4(a) — Polynomial-Time Multiplicity-Encoding Reduction from KNAPSACK to $n|1|r_n\ge 0, w_j=1|\sum w_j C_j$
-- statement:
--   There exists a polynomial-time computable function $f$ on $\mathrm{BSym}$ strings that maps binary-coded KNAPSACK instances $\mathrm{knapsackCode}(a, b)$ with $0 < b < A$ to multiplicity-encoded instances in $\mathrm{sumCLangMult}$ representing $(\mathrm{procTime}(a,b), \mathrm{weight}(a,b), \mathrm{release}(a,b), \mathrm{yThreshold}(a,b))$, and resolves boundary instances $b \ge A$.
-- source:
--   Brucker, Lenstra & Rinnooy Kan 1975, Complexity of Machine Scheduling Problems, Report BW 43/75, pp. 22–23, Theorem 4(a) and Remark

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
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SchedComplexity_TotalCompletion_Knapsack
import Definitions.Def_SchedComplexity_TotalCompletion_SingleMachine
import Definitions.Def_SchedComplexity_TotalCompletion_Construction

namespace SchedComplexity.TotalCompletion

open ProjSchedTW.Complexity (BSym encNats)

/-- Polynomial-time multiplicity-encoding reduction for Theorem 4(a) (Brucker, Lenstra &
Rinnooy Kan 1975, pp. 22–23, Remark p. 23): there is a polynomial-time computable function `f` on
`BSym` strings that maps binary-coded KNAPSACK instances `knapsackCode a b` with `0 < b < sumA a`
to multiplicity-encoded instances in `sumCLangMult` representing `(procTime a b, weight a b,
release a b, yThreshold a b)`, and handles boundary instances `b ≥ sumA a`. -/
theorem knapsack_mult_encoding_reduction :
    ∃ f : List BSym → List BSym, CookPvsNP.PolyTimeComputable f ∧
      ∀ x : List BSym,
        ((∃ (t : ℕ) (a : Fin t → ℕ) (b : ℕ),
            IsKnapsackInstance a b ∧ b < sumA a ∧
            IsYes (procTime a b) (weight a b) (release a b) (yThreshold a b) ∧
            x = knapsackCode a b) ∨
          (∃ (t : ℕ) (a : Fin t → ℕ) (b : ℕ),
            IsKnapsackInstance a b ∧ b = sumA a ∧ x = knapsackCode a b)) ↔
          f x ∈ sumCLangMult := by sorry

end SchedComplexity.TotalCompletion
