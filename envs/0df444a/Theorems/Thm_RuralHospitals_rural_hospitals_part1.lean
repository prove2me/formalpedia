-- Prove2me | Theorems.Thm_RuralHospitals_rural_hospitals_part1
-- name    : RuralHospitals.rural_hospitals_part1
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T15:19:43.64744+00:00
-- url     : https://prove2.me/theorems/022f446b-7d47-4803-9f04-d9407704cca9
-- title:
--   Rural hospitals theorem, Part 1
-- statement:
--   Consider a many-to-one matching market with a finite set $D$ of doctors and a finite set $H$ of hospitals, where hospital $h$ has $q_h$ positions and all preferences are strict. For a matching $\mu$, write $\mu(h)\subseteq D$ for the set of doctors assigned to $h$. Let $\mu$ and $\nu$ be stable matchings. Then
--
--   1. the set of assigned doctors is the same: for every $d\in D$, $d$ is matched under $\mu$ if and only if $d$ is matched under $\nu$;
--   2. the number of filled positions at each hospital is the same:
--
--   $$
--   |\mu(h)| = |\nu(h)| \qquad \text{for all } h\in H.
--   $$
--
--   This is Part 1 of the rural hospitals theorem (Roth 1984): changing the stable mechanism cannot change who is employed or how many positions each hospital fills.
--
--   **Formalization Note** Uses the model `RuralHospitals.Market` (definition `RuralHospitals_Market`): finite types `D` (doctors) and `H` (hospitals); strict preferences given by injective rank functions on `Option H` / `Option D` (smaller rank = preferred, `none` = unmatched / empty position); responsive hospital preferences; capacities `capacity : H → ℕ`. An assignment is a map `μ : D → Option H`, and `assigned μ h` is the finite set of doctors placed at `h`.
-- source:
--   Wikipedia, "Rural hospitals theorem", revision oldid=1064508418 (https://en.wikipedia.org/w/index.php?title=Rural_hospitals_theorem&oldid=1064508418), introduction, Part 1: "The set of assigned doctors, and the number of filled positions in each hospital, are the same in all stable matchings." Primary reference: A. E. Roth, The evolution of the labor market for medical interns and residents: a case study in game theory, J. Political Economy 92 (1984) 991–1016, doi:10.1086/261272.

import Mathlib
import Definitions.Def_RuralHospitals_Market

namespace RuralHospitals

theorem rural_hospitals_part1 {D H : Type*} [Fintype D] [Fintype H] [DecidableEq H]
    (M : Market D H) (μ ν : Assignment D H) (hμ : M.IsStable μ) (hν : M.IsStable ν) :
    (∀ d, (μ d).isSome = (ν d).isSome) ∧
      ∀ h, (assigned μ h).card = (assigned ν h).card := by sorry

end RuralHospitals
