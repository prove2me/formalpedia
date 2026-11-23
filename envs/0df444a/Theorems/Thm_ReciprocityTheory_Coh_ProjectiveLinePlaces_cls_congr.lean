-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_ProjectiveLinePlaces_cls_congr
-- name    : ReciprocityTheory.Coh.ProjectiveLinePlaces.cls_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:07.218884+00:00
-- url     : https://prove2.me/theorems/01e221a2-70bb-4c22-9a3d-fd325cf9c2ea
-- title:
--   Projective Line Places: cls congr
-- statement:
--   The Projective Line Places construction uses the cls congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/FiberFirstH0Injective.lean#L39-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/FiberFirstH0Injective.lean#L39-L40

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiberFirstH0Injective
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_congr
import Theorems.Thm_ReciprocityTheory_Coh_LongExactSequenceMaps_cls_congr

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

theorem ReciprocityTheory.Coh.ProjectiveLinePlaces.cls_congr (A : Cx R) (n : ℕ) {x y : A.X n} (hx hy) (e : x = y) : A.cls n x hx = A.cls n y hy := by sorry
