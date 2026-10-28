-- Prove2me | Theorems.Thm_SchedComplexity_Shops_knapsack_ghij_encoding_reduction
-- name    : SchedComplexity.Shops.knapsack_ghij_encoding_reduction
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-27T06:41:10.778118+00:00
-- url     : https://prove2.me/theorems/0265a395-687b-4df7-90d8-e515d7b7fe0d
-- title:
--   Theorem 4(g,h,i,j) — Polynomial-Time Binary Encoding Reductions from KNAPSACK to Flow Shop and Job Shop Problems
-- statement:
--   Establishes the existence of polynomial-time computable functions on $\mathrm{BSym}$ strings that map binary-coded KNAPSACK instances $\mathrm{encNats}(b :: a)$ with $0 < b < A$ to the binary encodings of $\mathrm{constrG}(a,b)$, $\mathrm{constrH}(a,b)$, $\mathrm{constrI}(a,b)$, and $\mathrm{constrJ}(a,b)$ in the four shop languages, and resolve boundary instances $b \ge A$.
-- source:
--   Brucker, Lenstra & Rinnooy Kan 1975, Complexity of Machine Scheduling Problems, Report BW 43/75, pp. 16–18, Theorem 4(g,h,i,j)

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
import Definitions.Def_SchedComplexity_Shops_Problems
import Definitions.Def_SchedComplexity_Shops_Constructions

namespace SchedComplexity.Shops

open CookPvsNP ProjSchedTW.Complexity

/-- Polynomial-time binary encoding reductions for Theorem 4(g), (h), (i), (j) (Brucker, Lenstra &
Rinnooy Kan 1975, pp. 16–18): maps `encNats (b :: a)` with `0 < b < a.sum` to the binary encodings
of `constrG a b`, `constrH a b`, `constrI a b`, and `constrJ a b` in the four target shop languages,
and handles boundary instances `b ≥ a.sum`. -/
theorem knapsack_ghij_encoding_reduction :
    (∃ fG : List BSym → List BSym, PolyTimeComputable fG ∧
      ∀ x : List BSym,
        ((∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b < a.sum ∧
            (constrG a b).HasScheduleLE (yG a) ∧ x = encNats (b :: a)) ∨
          (∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b = a.sum ∧ x = encNats (b :: a))) ↔
          fG x ∈ langFlowRn) ∧
    (∃ fH : List BSym → List BSym, PolyTimeComputable fH ∧
      ∀ x : List BSym,
        ((∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b < a.sum ∧
            (constrH a b).HasScheduleLE (yH a) ∧ x = encNats (b :: a)) ∨
          (∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b = a.sum ∧ x = encNats (b :: a))) ↔
          fH x ∈ langFlowTree) ∧
    (∃ fI : List BSym → List BSym, PolyTimeComputable fI ∧
      ∀ x : List BSym,
        ((∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b < a.sum ∧
            (constrI a b).HasScheduleLE (yI a) ∧ x = encNats (b :: a)) ∨
          (∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b = a.sum ∧ x = encNats (b :: a))) ↔
          fI x ∈ langJob2Ops3) ∧
    (∃ fJ : List BSym → List BSym, PolyTimeComputable fJ ∧
      ∀ x : List BSym,
        ((∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b < a.sum ∧
            (constrJ a b).HasScheduleLE (yJ a) ∧ x = encNats (b :: a)) ∨
          (∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ b = a.sum ∧ x = encNats (b :: a))) ↔
          fJ x ∈ langJob3Ops2) := by sorry

end SchedComplexity.Shops
