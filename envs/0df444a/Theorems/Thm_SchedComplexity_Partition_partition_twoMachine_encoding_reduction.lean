-- Prove2me | Theorems.Thm_SchedComplexity_Partition_partition_twoMachine_encoding_reduction
-- name    : SchedComplexity.Partition.partition_twoMachine_encoding_reduction
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-27T06:41:01.625993+00:00
-- url     : https://prove2.me/theorems/5284804a-178f-4ff4-b4a0-497268af572d
-- title:
--   Theorem 3(a,b) — Polynomial-Time Binary Encoding Reductions from PARTITION to Two-Machine Scheduling
-- statement:
--   Establishes the existence of polynomial-time computable functions on $\mathrm{BSym}$ strings that map $\mathrm{encNats}(a)$ for positive integers $a$ to $\mathrm{cmaxCode}$ and $\mathrm{sumWCCode}$ instances in $\mathrm{cmaxLang}$ and $\mathrm{sumWCLang}$ corresponding to $(\mathrm{procA}(a), y_A(a))$ and $(\mathrm{procB}(a), y_B(a))$.
-- source:
--   Brucker, Lenstra & Rinnooy Kan 1975, Complexity of Machine Scheduling Problems, Report BW 43/75, p. 15, Theorem 3(a,b)

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
import Definitions.Def_SchedComplexity_Partition_PartitionProblem
import Definitions.Def_SchedComplexity_Partition_Languages
import Definitions.Def_SchedComplexity_Partition_Constructions

namespace SchedComplexity.Partition

open ProjSchedTW.Complexity (BSym encNats)

/-- Polynomial-time binary encoding reductions for Theorem 3(a) and 3(b) (Brucker, Lenstra &
Rinnooy Kan 1975, p. 15): maps `encNats a` (for positive integers `a`) to `cmaxCode` and
`sumWCCode` instances in `cmaxLang` and `sumWCLang` corresponding to `procA a`, `yA a` and
`procB a`, `yB a`. -/
theorem partition_twoMachine_encoding_reduction :
    (∃ fA : List BSym → List BSym, CookPvsNP.PolyTimeComputable fA ∧
      ∀ c : List BSym,
        (∃ a : List ℕ, (∀ x ∈ a, 0 < x) ∧
          (∃ σ : Schedule a.length, σ.IsFeasible (procA a) ∧
            ∀ j, (σ.completion (procA a) j : ℝ) ≤ yA a) ∧
          c = encNats a) ↔ fA c ∈ cmaxLang) ∧
    (∃ fB : List BSym → List BSym, CookPvsNP.PolyTimeComputable fB ∧
      ∀ c : List BSym,
        (∃ a : List ℕ, (∀ x ∈ a, 0 < x) ∧
          (∃ σ : Schedule a.length, σ.IsFeasible (procB a) ∧
            (σ.sumWC (procB a) (procB a) : ℝ) ≤ yB a) ∧
          c = encNats a) ↔ fB c ∈ sumWCLang) := by sorry

end SchedComplexity.Partition
