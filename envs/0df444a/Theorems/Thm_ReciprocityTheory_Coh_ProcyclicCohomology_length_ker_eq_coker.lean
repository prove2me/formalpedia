-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_ProcyclicCohomology_length_ker_eq_coker
-- name    : ReciprocityTheory.Coh.ProcyclicCohomology.length_ker_eq_coker
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:57:23.371732+00:00
-- url     : https://prove2.me/theorems/6e7a0f57-8548-52ea-9c8a-ea74d3ca338b
-- title:
--   Procyclic Cohomology: length ker eq coker
-- statement:
--   The Procyclic Cohomology construction uses the length ker eq coker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/LengthKerEqCoker.lean#L21-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/LengthKerEqCoker.lean#L21-L34

import Definitions.Def_ReciprocityTheory_GroupCohomology_CardLenStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_LowHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_PairHomFCoeOfId
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_KilledHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiniteLevel
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiberFirstH0Injective
import Definitions.Def_ReciprocityTheory_GroupCohomology_ProdHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_EqZeroOfLe
import Definitions.Def_ReciprocityTheory_GroupCohomology_MemCoboundariesOfCocycleProcyclic
import Definitions.Def_ReciprocityTheory_GroupCohomology_LengthKerEqCoker
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Function
universe u
open ReciprocityTheory.Coh.ProcyclicCohomology

theorem ReciprocityTheory.Coh.ProcyclicCohomology.length_ker_eq_coker {R : Type u} [CommRing R] {V : Type u} [AddCommGroup V] [Module R V]
    (f : V →ₗ[R] V) (h : IsFiniteLength R V) :
    Module.length R (LinearMap.ker f) = Module.length R (V ⧸ LinearMap.range f) := by sorry
