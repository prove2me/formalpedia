-- Prove2me | Theorems.Thm_SchedComplexity_NoWait_dhp_noWait_encoding_reduction
-- name    : SchedComplexity.NoWait.dhp_noWait_encoding_reduction
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-27T06:41:01.567217+00:00
-- url     : https://prove2.me/theorems/16cc9186-9f1a-4a5e-8e3d-933abb90e1f9
-- title:
--   Theorem 5(a,b) — Polynomial-Time Binary Encoding Reductions from DIRECTED HAMILTON PATH to No-Wait Flow Shop
-- statement:
--   Establishes the existence of polynomial-time computable functions on $\mathrm{BSym}$ strings that map $\mathrm{dhpCode}(\mathrm{adj})$ (for $n \ne 2$) to $\mathrm{nwCode}(\mathrm{procTimes}(\mathrm{adj}, \iota, 1, 5), y)$ for an admissible machine assignment $\iota$ with $\lambda = 1, \mu = 5$, and directly resolve the $n = 2$ case.
-- source:
--   Brucker, Lenstra & Rinnooy Kan 1975, Complexity of Machine Scheduling Problems, Report BW 43/75, pp. 24–25, Theorem 5(a,b)

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
import Definitions.Def_SchedComplexity_NoWait_DirectedGraphs
import Definitions.Def_SchedComplexity_NoWait_NoWaitFlowShop
import Definitions.Def_SchedComplexity_NoWait_Construction

namespace SchedComplexity.NoWait

open ProjSchedTW.Complexity (BSym encNats)

/-- Polynomial-time binary encoding reductions for Theorem 5(a) and 5(b) (Brucker, Lenstra &
Rinnooy Kan 1975, pp. 24–25): maps `dhpCode adj` (for `n ≠ 2`) to `nwCode (procTimes adj ι 1 5) y`
for an admissible machine assignment `ι` with `λ = 1`, `μ = 5`, and directly resolves the `n = 2`
case. -/
theorem dhp_noWait_encoding_reduction :
    (∃ fA : List BSym → List BSym, CookPvsNP.PolyTimeComputable fA ∧
      ∀ w : List BSym,
        ((∃ (n : ℕ) (adj : Fin n → Fin n → Bool), n ≠ 2 ∧
            (∀ ι : Fin n → Fin n → ℕ, Admissible n ι →
              ∃ B, IsNoWaitSchedule (procTimes adj ι 1 5) B ∧
                ∀ ℓ, completion (procTimes adj ι 1 5) B ℓ ≤
                  (n - 1) * (5 + 2 * 1) + numMachines n * 5) ∧
            w = dhpCode adj) ∨
          (∃ adj : Fin 2 → Fin 2 → Bool, HasHamiltonPath adj ∧ w = dhpCode adj)) ↔
          fA w ∈ cmaxLang) ∧
    (∃ fB : List BSym → List BSym, CookPvsNP.PolyTimeComputable fB ∧
      ∀ w : List BSym,
        ((∃ (n : ℕ) (adj : Fin n → Fin n → Bool), n ≠ 2 ∧
            (∀ ι : Fin n → Fin n → ℕ, Admissible n ι →
              ∃ B, IsNoWaitSchedule (procTimes adj ι 1 5) B ∧
                ((∑ ℓ, completion (procTimes adj ι 1 5) B ℓ : ℕ) : ℚ) ≤
                  (1 / 2 : ℚ) * n * ((n : ℚ) - 1) * ((5 : ℚ) + 2 * 1) +
                    (n : ℚ) * (numMachines n : ℚ) * 5) ∧
            w = dhpCode adj) ∨
          (∃ adj : Fin 2 → Fin 2 → Bool, HasHamiltonPath adj ∧ w = dhpCode adj)) ↔
          fB w ∈ sumCLang) := by sorry

end SchedComplexity.NoWait
