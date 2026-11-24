-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_equiv_f121b6417e76
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_equiv_f121b6417e76
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:46.360742+00:00
-- url     : https://prove2.me/theorems/8477bc4e-5a28-40c6-ac84-afccecc81ea3
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Objects equiv f121b6417e76: P2 M Ground Theory Heights  Heights Numbers DVR Objects equiv f121b6417e76
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Objects equiv f121b6417e76 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Objects equiv f121b6417e76 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisorAlt.lean#L114-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisorAlt.lean#L114-L125

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.Objects
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_equiv_f121b6417e76 (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    (∀ (f : MRing ι O) (b : K → ℕ), IsMultiHomog f b ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f b) ∧
    (∀ P : Ideal (MRing ι O), IsMultiProjPrime P ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime P) ∧
    (∀ (P : Ideal (MRing ι O)) (s : MRing ι O) (W : Ideal (MRing ι O)),
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.intCyc (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) W =
        divCycle P s W) ∧
    (∀ (P : Ideal (MRing ι O)) (f g : MRing ι O) (W : Ideal (MRing ι O)),
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.divO P f g W = ratDiv P f g W) ∧
    (∀ (J : Ideal (MRing ι (IsLocalRing.ResidueField O)) → ℤ) (Z : Ideal (MRing ι O) →₀ ℤ),
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.redEval J Z =
        cycEval (fun W => J (specialIdeal W)) Z) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«Objects».«equiv» := P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_equiv_f121b6417e76
