-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_LongExactSequenceMaps_H_cls
-- name    : ReciprocityTheory.Coh.LongExactSequenceMaps.H_cls
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:28:35.893738+00:00
-- url     : https://prove2.me/theorems/93cebab4-4a3e-4aac-9849-7e62d74d25fb
-- title:
--   Long Exact Sequence Maps: H cls
-- statement:
--   The Long Exact Sequence Maps construction uses the H cls property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/ConnNatHolds.lean#L35-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/ConnNatHolds.lean#L35-L36

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_H_cls
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
universe u
open ReciprocityTheory.Coh.LongExactSequenceMaps
variable {R : Type u} [CommRing R] {A B C : Cx R}

theorem ReciprocityTheory.Coh.LongExactSequenceMaps.H_cls (φ : Hom A B) (n : ℕ) (x : A.X n) (hx : A.d n x = 0) :
    φ.H n (A.cls n x hx) = B.cls n (φ.f n x) (by rw [← φ.comm, hx, map_zero]) := by sorry
