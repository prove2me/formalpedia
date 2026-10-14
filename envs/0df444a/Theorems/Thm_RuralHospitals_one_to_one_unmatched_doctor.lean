-- Prove2me | Theorems.Thm_RuralHospitals_one_to_one_unmatched_doctor
-- name    : RuralHospitals.one_to_one_unmatched_doctor
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T15:18:06.174915+00:00
-- url     : https://prove2.me/theorems/18159206-2db0-4175-b963-cf709c7efffd
-- title:
--   Rural hospitals theorem, one-position case: unmatched doctors
-- statement:
--   Consider a matching market with a finite set $D$ of doctors and a finite set $H$ of hospitals, in which **every hospital has exactly one position** and all preferences are strict. Let $A$ and $B$ be two stable matchings. For every doctor $d\in D$,
--
--   $$
--   d \text{ is unmatched in } A \implies d \text{ is unmatched in } B.
--   $$
--
--   This is the doctor half of Part 1 of the rural hospitals theorem in the special case of one position per hospital (the stable marriage setting with unequal sides), first proved by McVitie and Wilson (1970).
--
--   **Formalization Note** Uses the model `RuralHospitals.Market` (definition `RuralHospitals_Market`): finite types `D` (doctors) and `H` (hospitals); strict preferences given by injective rank functions on `Option H` / `Option D` (smaller rank = preferred, `none` = unmatched / empty position); responsive hospital preferences; capacities `capacity : H → ℕ`. An assignment is a map `μ : D → Option H`, and `assigned μ h` is the finite set of doctors placed at `h`.
-- source:
--   Wikipedia, "Rural hospitals theorem", revision oldid=1064508418 (https://en.wikipedia.org/w/index.php?title=Rural_hospitals_theorem&oldid=1064508418), section "Proof of a special case": "Hence, if d0 is unmatched in A, he must be unmatched in B too." Primary reference: D. G. McVitie, L. B. Wilson, Stable marriage assignment for unequal sets, BIT 10 (1970) 295–309, doi:10.1007/BF01934199.

import Mathlib
import Definitions.Def_RuralHospitals_Market

namespace RuralHospitals

theorem one_to_one_unmatched_doctor {D H : Type*} [Fintype D] [Fintype H] [DecidableEq H]
    (M : Market D H) (hcap : ∀ h, M.capacity h = 1) (μ ν : Assignment D H)
    (hμ : M.IsStable μ) (hν : M.IsStable ν) (d : D) (hd : μ d = none) :
    ν d = none := by sorry

end RuralHospitals
