-- Prove2me | Theorems.Thm_P2M_GroundTheory_ProfCoh_inflationCochains_comp_cochainsComplex__38875cb65454
-- name    : P2M_GroundTheory_ProfCoh_inflationCochains_comp_cochainsComplex__38875cb65454
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:16:42.982104+00:00
-- url     : https://prove2.me/theorems/352535a3-c6df-47d1-8512-801a369f4dbc
-- title:
--   P2 M Ground Theory Prof Coh inflation Cochains comp cochains Complex  38875cb65454: P2 M Ground Theory Prof Coh inflation Cochains comp cochains Complex  38875cb65454
-- statement:
--   The P2 M Ground Theory Prof Coh inflation Cochains comp cochains Complex  38875cb65454 construction uses the P2 M Ground Theory Prof Coh inflation Cochains comp cochains Complex  38875cb65454 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ColimitDefs.lean#L125-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ColimitDefs.lean#L125-L128

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_Functoriality
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
import Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitDefs
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
variable (A : Rep.{u} k G)
variable [IsTopologicalGroup G] [IsDiscreteRep A]

theorem P2M_GroundTheory_ProfCoh_inflationCochains_comp_cochainsComplex__38875cb65454 (U : OpenNormalSubgroup G) :
    inflationCochains A U ≫ cochainsComplexι A = infCochains A U := by sorry

alias «GroundTheory».«ProfCoh».«inflationCochains_comp_cochainsComplexι» := P2M_GroundTheory_ProfCoh_inflationCochains_comp_cochainsComplex__38875cb65454
