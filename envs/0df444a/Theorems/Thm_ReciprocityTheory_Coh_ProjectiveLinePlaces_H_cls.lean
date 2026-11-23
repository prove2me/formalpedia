-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_ProjectiveLinePlaces_H_cls
-- name    : ReciprocityTheory.Coh.ProjectiveLinePlaces.H_cls
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:43:07.776264+00:00
-- url     : https://prove2.me/theorems/352b06f1-2fcc-49d9-9fa4-f9ef30ca3d33
-- title:
--   Projective Line Places: H cls
-- statement:
--   The Projective Line Places construction uses the H cls property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/FiberFirstH0Injective.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/FiberFirstH0Injective.lean#L20-L21

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiberFirstH0Injective
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_H_cls
import Theorems.Thm_ReciprocityTheory_Coh_LongExactSequenceMaps_H_cls
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.H_cls


set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open Cx Function
noncomputable section
universe u
open ReciprocityTheory.Coh.ProjectiveLinePlaces
variable {R : Type u} [CommRing R] {A B : Cx R}

theorem ReciprocityTheory.Coh.ProjectiveLinePlaces.H_cls (φ : Hom A B) (n : ℕ) (x : A.X n) (hx) :
    φ.H n (A.cls n x hx) = B.cls n (φ.f n x) (by rw [← φ.comm, hx, map_zero]) := by sorry
