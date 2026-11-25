-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_isFiniteLength_of_exact
-- name    : ReciprocityTheory.Coh.isFiniteLength_of_exact
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:03:54.650387+00:00
-- url     : https://prove2.me/theorems/81074677-2590-537d-bb65-73e6e5ae1285
-- title:
--   Coh: is Finite Length of exact
-- statement:
--   The Coh construction uses the is Finite Length of exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/FinGen.lean#L60-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/FinGen.lean#L60-L67

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_IsSuccSubset
import Definitions.Def_ReciprocityTheory_GroupCohomology_FinGen
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
universe u
variable {R : Type u} [CommRing R] {M P Q : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]

theorem ReciprocityTheory.Coh.isFiniteLength_of_exact {N : Type*} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : Exact f g)
    (hM : IsFiniteLength R M) (hP : IsFiniteLength R P) : IsFiniteLength R N := by sorry
