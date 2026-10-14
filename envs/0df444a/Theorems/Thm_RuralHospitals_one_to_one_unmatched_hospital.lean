-- Prove2me | Theorems.Thm_RuralHospitals_one_to_one_unmatched_hospital
-- name    : RuralHospitals.one_to_one_unmatched_hospital
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T15:19:15.326409+00:00
-- url     : https://prove2.me/theorems/3e027b12-5c38-4b04-be7e-f0a1d41e20a4
-- title:
--   Rural hospitals theorem, one-position case: unmatched hospitals
-- statement:
--   Consider a matching market with a finite set $D$ of doctors and a finite set $H$ of hospitals, in which **every hospital has exactly one position** and all preferences are strict. Let $A$ and $B$ be two stable matchings. For every hospital $h\in H$,
--
--   $$
--   A(h)=\varnothing \implies B(h)=\varnothing,
--   $$
--
--   where $A(h)$ denotes the set of doctors assigned to $h$ in $A$. In words: a hospital unmatched in one stable matching is unmatched in every stable matching.
--
--   This is the hospital half of Part 1 of the rural hospitals theorem in the one-position special case (McVitie–Wilson 1970).
--
--   **Formalization Note** Uses the model `RuralHospitals.Market` (definition `RuralHospitals_Market`): finite types `D` (doctors) and `H` (hospitals); strict preferences given by injective rank functions on `Option H` / `Option D` (smaller rank = preferred, `none` = unmatched / empty position); responsive hospital preferences; capacities `capacity : H → ℕ`. An assignment is a map `μ : D → Option H`, and `assigned μ h` is the finite set of doctors placed at `h`.
-- source:
--   Wikipedia, "Rural hospitals theorem", revision oldid=1064508418 (https://en.wikipedia.org/w/index.php?title=Rural_hospitals_theorem&oldid=1064508418), section "Proof of a special case": "The same is true for the hospitals: any hospital that is unmatched in A, must be unmatched in B too." Primary reference: McVitie–Wilson, BIT 10 (1970) 295–309, doi:10.1007/BF01934199.

import Mathlib
import Definitions.Def_RuralHospitals_Market

namespace RuralHospitals

theorem one_to_one_unmatched_hospital {D H : Type*} [Fintype D] [Fintype H] [DecidableEq H]
    (M : Market D H) (hcap : ∀ h, M.capacity h = 1) (μ ν : Assignment D H)
    (hμ : M.IsStable μ) (hν : M.IsStable ν) (h : H) (hh : assigned μ h = ∅) :
    assigned ν h = ∅ := by sorry

end RuralHospitals
