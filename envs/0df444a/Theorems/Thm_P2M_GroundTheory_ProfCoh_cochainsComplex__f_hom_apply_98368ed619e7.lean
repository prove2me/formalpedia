-- Prove2me | Theorems.Thm_P2M_GroundTheory_ProfCoh_cochainsComplex__f_hom_apply_98368ed619e7
-- name    : P2M_GroundTheory_ProfCoh_cochainsComplex__f_hom_apply_98368ed619e7
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:42:41.596051+00:00
-- url     : https://prove2.me/theorems/b8313370-a0c1-551d-9f2d-dbf3f648824c
-- title:
--   P2 M Ground Theory Prof Coh cochains Complex  f hom apply 98368ed619e7: P2 M Ground Theory Prof Coh cochains Complex  f hom apply 98368ed619e7
-- statement:
--   The P2 M Ground Theory Prof Coh cochains Complex  f hom apply 98368ed619e7 construction uses the P2 M Ground Theory Prof Coh cochains Complex  f hom apply 98368ed619e7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ContinuousCochains.lean#L116-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ContinuousCochains.lean#L116-L119

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules_IsDiscreteRepIffForallExistsOpenNormalSubgroup
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory groupCohomology
universe u
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G]
variable [IsTopologicalGroup G]

theorem P2M_GroundTheory_ProfCoh_cochainsComplex__f_hom_apply_98368ed619e7 (A : Rep.{u} k G) [IsDiscreteRep A] (n : ℕ)
    (f : locallyConstantCochains A n) :
    ((cochainsComplexι A).f n).hom f = (f : (Fin n → G) → A) := by sorry

alias «GroundTheory».«ProfCoh».«cochainsComplexι_f_hom_apply» := P2M_GroundTheory_ProfCoh_cochainsComplex__f_hom_apply_98368ed619e7
