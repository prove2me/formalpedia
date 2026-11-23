-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_InflationTower_Is_anti
-- name    : ReciprocityTheory.Coh.InflationTower.Is_anti
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:41.533264+00:00
-- url     : https://prove2.me/theorems/180373d0-130f-44c4-9006-06932c81f872
-- title:
--   Inflation Tower: Is anti
-- statement:
--   The Inflation Tower construction uses the Is anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/IsSuccSubset.lean#L146-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/IsSuccSubset.lean#L146-L148

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_IsSuccSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
noncomputable section
universe u
open Cx
open ReciprocityTheory.Coh.InflationTower
variable {R : Type u} [CommRing R]
variable (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m)) (k : ℕ) (c : ∀ m, (A m).X (k + 1))

theorem ReciprocityTheory.Coh.InflationTower.Is_anti (hc : ∀ m, (τ m).f (k+1) (c (m+1)) = c m) (m : ℕ) :
    Antitone fun j => Is A τ k c j m := by sorry
