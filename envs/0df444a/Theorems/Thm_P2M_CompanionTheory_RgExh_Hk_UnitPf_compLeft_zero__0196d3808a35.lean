-- Prove2me | Theorems.Thm_P2M_CompanionTheory_RgExh_Hk_UnitPf_compLeft_zero__0196d3808a35
-- name    : P2M_CompanionTheory_RgExh_Hk_UnitPf_compLeft_zero__0196d3808a35
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:32:23.459506+00:00
-- url     : https://prove2.me/theorems/4528ab58-61de-50ca-b597-3ada86ec5f21
-- title:
--   P2 M Companion Theory Rg Exh Hk Unit Pf comp Left zero  0196d3808a35: P2 M Companion Theory Rg Exh Hk Unit Pf comp Left zero  0196d3808a35
-- statement:
--   The P2 M Companion Theory Rg Exh Hk Unit Pf comp Left zero  0196d3808a35 construction uses the P2 M Companion Theory Rg Exh Hk Unit Pf comp Left zero  0196d3808a35 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/HeckeUnitTensors/CompLeftSmulOne.lean#L40-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/HeckeUnitTensors/CompLeftSmulOne.lean#L40-L41

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_ContOfFnProd
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_CompLeftSmulOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open CompanionTheory CompanionTheory.RgExh CompanionTheory.RgExh.Hk CompanionTheory.RgExh.Hk.UnitPf
open Formalism.REAL (qdet qminor Tm GlRel)
open Formalism.QuantumDeterminants (capP)
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (cminor)
open CompanionTheory.RgExh
variable {m : ℕ} (X : GMod (m + 1)) (χ : Fin (m + 1) → ℂ) (s : Fin (m + 1))
variable {X χ s}

theorem P2M_CompanionTheory_RgExh_Hk_UnitPf_compLeft_zero__0196d3808a35 : (0 : Module.End ℂ X.V).compLeft (Fin (m + 1)) = 0 := by sorry

alias «CompanionTheory».«RgExh».«Hk».«UnitPf».«compLeft_zero'» := P2M_CompanionTheory_RgExh_Hk_UnitPf_compLeft_zero__0196d3808a35
