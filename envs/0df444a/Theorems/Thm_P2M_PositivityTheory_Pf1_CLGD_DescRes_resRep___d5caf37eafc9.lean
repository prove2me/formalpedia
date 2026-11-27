-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Pf1_CLGD_DescRes_resRep___d5caf37eafc9
-- name    : P2M_PositivityTheory_Pf1_CLGD_DescRes_resRep___d5caf37eafc9
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T17:58:35.701558+00:00
-- url     : https://prove2.me/theorems/37f03a59-58a6-4e17-bc9b-6fd90471c160
-- title:
--   P2 M Positivity Theory Pf1 CLGD Desc Res res Rep   d5caf37eafc9: P2 M Positivity Theory Pf1 CLGD Desc Res res Rep   d5caf37eafc9
-- statement:
--   The P2 M Positivity Theory Pf1 CLGD Desc Res res Rep   d5caf37eafc9 construction uses the P2 M Positivity Theory Pf1 CLGD Desc Res res Rep   d5caf37eafc9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/LocalGlobalCompatibility/NormVEqPowResF.lean#L160-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/LocalGlobalCompatibility/NormVEqPowResF.lean#L160-L160

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_LocalGlobalCompatibility_NormVEqPowResF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open scoped Pointwise Topology
open PositivityTheory PositivityTheory.Pf1 PositivityTheory.Pf1.CLGD PositivityTheory.Pf1.CLGD.DescRes
variable {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω]
  [Algebra E E'] [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {w' : HeightOneSpectrum (𝓞 E')}
  (h : IsPlaceOver A w) (h' : IsPlaceOver A w')
  {V V' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

theorem P2M_PositivityTheory_Pf1_CLGD_DescRes_resRep___d5caf37eafc9 (a : WDRep h V) (σ : ↥(Weil h')) : (resRep h h' a).ρ σ = a.ρ (resW h h' σ) := by sorry

alias «PositivityTheory».«Pf1».«CLGD».«DescRes».«resRep_ρ» := P2M_PositivityTheory_Pf1_CLGD_DescRes_resRep___d5caf37eafc9

attribute [defeq] P2M_PositivityTheory_Pf1_CLGD_DescRes_resRep___d5caf37eafc9
