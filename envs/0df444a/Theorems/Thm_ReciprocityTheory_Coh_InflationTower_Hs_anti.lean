-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_InflationTower_Hs_anti
-- name    : ReciprocityTheory.Coh.InflationTower.Hs_anti
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:50:03.918723+00:00
-- url     : https://prove2.me/theorems/0f57a610-7761-4a13-8215-b929e4fb6091
-- title:
--   Inflation Tower: Hs anti
-- statement:
--   The Inflation Tower construction uses the Hs anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/IsSuccSubset.lean#L150-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/IsSuccSubset.lean#L150-L151

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

theorem ReciprocityTheory.Coh.InflationTower.Hs_anti (m : ℕ) : Antitone fun j => Hs A τ k j m := by sorry
