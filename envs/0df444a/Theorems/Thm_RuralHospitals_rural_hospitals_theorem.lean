-- Prove2me | Theorems.Thm_RuralHospitals_rural_hospitals_theorem
-- name    : RuralHospitals.rural_hospitals_theorem
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T15:21:21.775337+00:00
-- url     : https://prove2.me/theorems/812d8ca0-25b5-4ac7-9ddb-c21e39be5187
-- title:
--   Rural hospitals theorem
-- statement:
--   Consider a many-to-one matching market with a finite set $D$ of doctors and a finite set $H$ of hospitals, where hospital $h$ has $q_h$ positions and all preferences are strict. For a matching $\mu$, write $\mu(h)\subseteq D$ for the set of doctors assigned to $h$. Let $\mu$ and $\nu$ be any two stable matchings. Then
--
--   1. a doctor is matched under $\mu$ if and only if she is matched under $\nu$;
--   2. every hospital fills the same number of positions: $|\mu(h)|=|\nu(h)|$ for all $h\in H$;
--   3. every hospital with an empty position under $\mu$ receives the same doctors under $\nu$:
--
--   $$
--   |\mu(h)|<q_h \implies \nu(h)=\mu(h).
--   $$
--
--   This is the rural hospitals theorem (Roth 1984, 1986): as long as the mechanism produces stable matchings, changing it cannot give under-subscribed ("rural") hospitals more doctors or different doctors.
--
--   **Formalization Note** Uses the model `RuralHospitals.Market` (definition `RuralHospitals_Market`): finite types `D` (doctors) and `H` (hospitals); strict preferences given by injective rank functions on `Option H` / `Option D` (smaller rank = preferred, `none` = unmatched / empty position); responsive hospital preferences; capacities `capacity : H → ℕ`. An assignment is a map `μ : D → Option H`, and `assigned μ h` is the finite set of doctors placed at `h`.
-- source:
--   Wikipedia, "Rural hospitals theorem", revision oldid=1064508418 (https://en.wikipedia.org/w/index.php?title=Rural_hospitals_theorem&oldid=1064508418), introduction (the theorem and its two parts). Primary references: Roth, J. Political Economy 92 (1984) 991–1016, doi:10.1086/261272; Roth, Econometrica 54 (1986) 425–427, doi:10.2307/1913160.

import Mathlib
import Definitions.Def_RuralHospitals_Market

namespace RuralHospitals

theorem rural_hospitals_theorem {D H : Type*} [Fintype D] [Fintype H] [DecidableEq H]
    (M : Market D H) (μ ν : Assignment D H) (hμ : M.IsStable μ) (hν : M.IsStable ν) :
    (∀ d, (μ d).isSome = (ν d).isSome) ∧
      (∀ h, (assigned μ h).card = (assigned ν h).card) ∧
      ∀ h, (assigned μ h).card < M.capacity h → assigned ν h = assigned μ h := by sorry

end RuralHospitals
