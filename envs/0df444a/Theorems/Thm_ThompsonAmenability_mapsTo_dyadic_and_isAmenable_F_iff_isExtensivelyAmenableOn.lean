-- Prove2me | Theorems.Thm_ThompsonAmenability_mapsTo_dyadic_and_isAmenable_F_iff_isExtensivelyAmenableOn
-- name    : ThompsonAmenability.mapsTo_dyadic_and_isAmenable_F_iff_isExtensivelyAmenableOn
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-09-30T18:50:52.033991+00:00
-- url     : https://prove2.me/theorems/c7bf7b0c-d905-4721-a2c6-b010d814b0ea
-- title:
--   Chornyi Corollary 3 — F is amenable iff its action on the dyadics is extensively amenable
-- statement:
--   Let $X$ be the set of dyadic rationals in $(0,1)$. Every element of Thompson's group $F$ maps $X$ to itself, and $F$ is amenable if and only if its action on $X$ is extensively amenable.
--
--   **Formalization Note.** The action is evaluation of the elements of $F$, order isomorphisms of $[0,1]$, at points. Extensive amenability is stated for the action on $[0,1]$ relative to $X$ (`IsExtensivelyAmenableOn F UI X`), which is the action on $X$ once $F$ maps $X$ to itself; the statement includes that fact, which the source takes for granted in "its action on $X$".
-- source:
--   Chornyi, M., Superharmonic functions on the lamplighter graph of Thompson's group F (2019), https://arxiv.org/abs/1907.01440v1, p. 7, Corollary 3

import Mathlib
import Definitions.Def_Garrido_Amenability
import Definitions.Def_CannonFloydParry
import Definitions.Def_ThompsonAmenability

namespace ThompsonAmenability

theorem mapsTo_dyadic_and_isAmenable_F_iff_isExtensivelyAmenableOn :
    (∀ g : CannonFloydParry.F, ∀ x : CannonFloydParry.UI, (0 < (x : ℝ) ∧ (x : ℝ) < 1 ∧ CannonFloydParry.IsDyadic x) →
      0 < ((g • x : CannonFloydParry.UI) : ℝ) ∧ ((g • x : CannonFloydParry.UI) : ℝ) < 1 ∧ CannonFloydParry.IsDyadic (g • x : CannonFloydParry.UI)) ∧
    (Garrido.IsAmenable CannonFloydParry.F ↔
      IsExtensivelyAmenableOn CannonFloydParry.F CannonFloydParry.UI {x : CannonFloydParry.UI | 0 < (x : ℝ) ∧ (x : ℝ) < 1 ∧ CannonFloydParry.IsDyadic x}) := by
  sorry

end ThompsonAmenability
