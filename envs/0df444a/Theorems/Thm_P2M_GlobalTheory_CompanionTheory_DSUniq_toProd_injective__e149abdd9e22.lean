-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_DSUniq_toProd_injective__e149abdd9e22
-- name    : P2M_GlobalTheory_CompanionTheory_DSUniq_toProd_injective__e149abdd9e22
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:28:33.848222+00:00
-- url     : https://prove2.me/theorems/af938c2a-a036-4254-99bf-44a713737e56
-- title:
--   P2 M Global Theory Companion Theory DSUniq to Prod injective  e149abdd9e22: P2 M Global Theory Companion Theory DSUniq to Prod injective  e149abdd9e22
-- statement:
--   The P2 M Global Theory Companion Theory DSUniq to Prod injective  e149abdd9e22 construction uses the P2 M Global Theory Companion Theory DSUniq to Prod injective  e149abdd9e22 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsDerivedOnOfIsKMod.lean#L250-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsDerivedOnOfIsKMod.lean#L250-L255

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOnePOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Closure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_SopNegComm
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsDerivedOnOfIsKMod
import Theorems.Thm_CompanionTheory_D_LK_cyc_stab
import Theorems.Thm_CompanionTheory_D_LK_mem_cyc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset WithLp
open scoped InnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSUniq
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight Cas)
open PI.UpqRep (lowK IsURepOn IsIrredOn UJset IsDS)
open CompanionTheory.D.DSIC (KUnit KStab)
open CompanionTheory.D.LK (Cyc LocFin IsMin IsKMod MultAlg KModExists OrthCyc mem_cyc cyc_stab ev)
open ReciprocityTheory.ChartRestriction.DS (genSub IsDerivedOn)
open ReciprocityTheory.ChartRestriction.DS.USum (sD sE sσ ofP toP lift)
variable {n : ℕ}
variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {D : Submodule ℂ H} {D' : Submodule ℂ H'} {E : Fin n → Fin n → Module.End ℂ D}
  {E' : Fin n → Fin n → Module.End ℂ D'} {ε : Fin n → Bool}

theorem P2M_GlobalTheory_CompanionTheory_DSUniq_toProd_injective__e149abdd9e22 {x y : sD D D'} (h : toP x = toP y) : x = y := by sorry

alias «GlobalTheory».«CompanionTheory».«DSUniq».«toProd_injective₂» := P2M_GlobalTheory_CompanionTheory_DSUniq_toProd_injective__e149abdd9e22
