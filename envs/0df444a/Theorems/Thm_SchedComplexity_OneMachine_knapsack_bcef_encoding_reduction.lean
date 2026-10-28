-- Prove2me | Theorems.Thm_SchedComplexity_OneMachine_knapsack_bcef_encoding_reduction
-- name    : SchedComplexity.OneMachine.knapsack_bcef_encoding_reduction
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-27T06:41:07.111322+00:00
-- url     : https://prove2.me/theorems/e57a4895-08b8-4ef9-90c1-1db8bda37372
-- title:
--   Theorem 4(b,c,e,f) — Polynomial-Time Binary Encoding Reductions from KNAPSACK to Single-Machine Problems
-- statement:
--   Establishes the existence of polynomial-time computable functions on $\mathrm{BSym}$ strings that map binary-coded KNAPSACK instances $\mathrm{encNats}(b :: a)$ with $0 < b < A$ to the binary encodings of $\mathrm{instB}(a,b)$, $\mathrm{instCF}(a,b)$, and $\mathrm{instE}(a,b)$ in the four target single-machine languages, and resolve boundary instances $b \ge A$.
-- source:
--   Brucker, Lenstra & Rinnooy Kan 1975, Complexity of Machine Scheduling Problems, Report BW 43/75, pp. 16–19, Theorem 4(b,c,e,f)

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
import Definitions.Def_SchedComplexity_OneMachine_Knapsack
import Definitions.Def_SchedComplexity_OneMachine_Problems
import Definitions.Def_SchedComplexity_OneMachine_Constructions

namespace SchedComplexity.OneMachine

open CookPvsNP ProjSchedTW.Complexity

/-- Polynomial-time binary encoding reductions for Theorem 4(b), (c), (e), (f) (Brucker, Lenstra &
Rinnooy Kan 1975, pp. 16–19): maps `encNats (b :: a)` with `0 < b < a.sum` to the binary encodings
of `instB a b`, `instCF a b`, and `instE a b` in the four target languages, and handles boundary
instances `b ≥ a.sum`. -/
theorem knapsack_bcef_encoding_reduction :
    (∃ fB : List BSym → List BSym, PolyTimeComputable fB ∧
      ∀ x : List BSym,
        ((∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b < a.sum ∧
            (∃ B, (instB a b).IsFeasible B ∧ (∀ j, (instB a b).C B j ≤ (instB a b).d j) ∧
              (instB a b).sumWC B ≤ yB a b) ∧ x = encNats (b :: a)) ∨
          (∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b = a.sum ∧ x = encNats (b :: a))) ↔
          fB x ∈ langLmaxSumWC) ∧
    (∃ fC : List BSym → List BSym, PolyTimeComputable fC ∧
      ∀ x : List BSym,
        ((∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b < a.sum ∧
            (∃ B, (instCF a b).IsFeasible B ∧ ∀ j, (instCF a b).lateness B j ≤ 0) ∧
            x = encNats (b :: a)) ∨
          (∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b = a.sum ∧ x = encNats (b :: a))) ↔
          fC x ∈ langRnLmax) ∧
    (∃ fE : List BSym → List BSym, PolyTimeComputable fE ∧
      ∀ x : List BSym,
        ((∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b < a.sum ∧
            (∃ B, (instE a b).IsFeasible B ∧ (instE a b).sumWU B ≤ yE a b) ∧
            x = encNats (b :: a)) ∨
          (∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b = a.sum ∧ x = encNats (b :: a))) ↔
          fE x ∈ langSumWU) ∧
    (∃ fF : List BSym → List BSym, PolyTimeComputable fF ∧
      ∀ x : List BSym,
        ((∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b < a.sum ∧
            (∃ B, (instCF a b).IsFeasible B ∧ (instCF a b).sumWU B ≤ 0) ∧
            x = encNats (b :: a)) ∨
          (∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b = a.sum ∧ x = encNats (b :: a))) ↔
          fF x ∈ langRnUnitSumWU) := by sorry

end SchedComplexity.OneMachine
