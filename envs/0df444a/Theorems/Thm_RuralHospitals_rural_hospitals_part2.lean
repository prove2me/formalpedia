-- Prove2me | Theorems.Thm_RuralHospitals_rural_hospitals_part2
-- name    : RuralHospitals.rural_hospitals_part2
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T15:20:42.836058+00:00
-- url     : https://prove2.me/theorems/c1c228ec-7e4a-4a73-838a-3ad7dda2ad69
-- title:
--   Rural hospitals theorem, Part 2
-- statement:
--   Consider a many-to-one matching market with a finite set $D$ of doctors and a finite set $H$ of hospitals, where hospital $h$ has $q_h$ positions and all preferences are strict. For a matching $\mu$, write $\mu(h)\subseteq D$ for the set of doctors assigned to $h$. Let $\mu$ and $\nu$ be stable matchings and let $h\in H$ be a hospital with an empty position under $\mu$, i.e. $|\mu(h)|<q_h$. Then
--
--   $$
--   \nu(h)=\mu(h).
--   $$
--
--   This is Part 2 of the rural hospitals theorem (Roth 1986): an under-subscribed hospital receives exactly the same set of doctors in every stable matching.
--
--   **Formalization Note** Uses the model `RuralHospitals.Market` (definition `RuralHospitals_Market`): finite types `D` (doctors) and `H` (hospitals); strict preferences given by injective rank functions on `Option H` / `Option D` (smaller rank = preferred, `none` = unmatched / empty position); responsive hospital preferences; capacities `capacity : H → ℕ`. An assignment is a map `μ : D → Option H`, and `assigned μ h` is the finite set of doctors placed at `h`.
-- source:
--   Wikipedia, "Rural hospitals theorem", revision oldid=1064508418 (https://en.wikipedia.org/w/index.php?title=Rural_hospitals_theorem&oldid=1064508418), introduction, Part 2: "Any hospital that has some empty positions in some stable matching, receives exactly the same set of doctors in all stable matchings." Primary reference: A. E. Roth, On the allocation of residents to rural hospitals: a general property of two-sided matching markets, Econometrica 54 (1986) 425–427, doi:10.2307/1913160.

import Mathlib
import Definitions.Def_RuralHospitals_Market

namespace RuralHospitals

theorem rural_hospitals_part2 {D H : Type*} [Fintype D] [Fintype H] [DecidableEq H]
    (M : Market D H) (μ ν : Assignment D H) (hμ : M.IsStable μ) (hν : M.IsStable ν)
    (h : H) (hh : (assigned μ h).card < M.capacity h) :
    assigned ν h = assigned μ h := by sorry

end RuralHospitals
