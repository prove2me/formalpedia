-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_shp_bij_of_inv
-- name    : ReciprocityTheory.Coh.shp_bij_of_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:43:52.384249+00:00
-- url     : https://prove2.me/theorems/9ae86688-5ef1-42dc-ab91-45b80a3c3c56
-- title:
--   Coh: shp bij of inv
-- statement:
--   The Coh construction uses the shp bij of inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/Shapiro.lean#L26-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/Shapiro.lean#L26-L45

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogIso
import Definitions.Def_ReciprocityTheory_GroupCohomology_PrismOpZeroEval
import Definitions.Def_ReciprocityTheory_GroupCohomology_Shapiro
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R] {A B : Cx R}

theorem ReciprocityTheory.Coh.shp_bij_of_inv (φ : Hom A B) (ψ : Hom B A) (n : ℕ) (h1 : (ψ.comp φ).H n = (Hom.id A).H n)
    (h2 : (φ.comp ψ).H n = (Hom.id B).H n) : Bijective (φ.H n) := by sorry
