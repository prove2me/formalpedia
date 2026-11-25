-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_ProjectiveLinePlaces_cls_eq_zero
-- name    : ReciprocityTheory.Coh.ProjectiveLinePlaces.cls_eq_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:51:34.166224+00:00
-- url     : https://prove2.me/theorems/3ee812d3-c514-51e6-990f-fe211df772a5
-- title:
--   Projective Line Places: cls eq zero
-- statement:
--   The Projective Line Places construction uses the cls eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/FiberFirstH0Injective.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/FiberFirstH0Injective.lean#L13-L14

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiberFirstH0Injective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open Cx Function
noncomputable section
universe u
open ReciprocityTheory.Coh.ProjectiveLinePlaces
variable {R : Type u} [CommRing R] {A B : Cx R}

theorem ReciprocityTheory.Coh.ProjectiveLinePlaces.cls_eq_zero (A : Cx R) (n : ℕ) (x : A.X n) (hx) : A.cls n x hx = 0 ↔ x ∈ A.B n := by sorry
