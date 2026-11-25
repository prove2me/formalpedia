-- Prove2me | Theorems.Thm_P2M_CompanionTheory_RgExh_Hk_UnitPf_mem_of_eig__4ecd2e63b290
-- name    : P2M_CompanionTheory_RgExh_Hk_UnitPf_mem_of_eig__4ecd2e63b290
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:04:30.871077+00:00
-- url     : https://prove2.me/theorems/0bd4521e-9df6-4d79-97f0-dbf28314cc16
-- title:
--   P2 M Companion Theory Rg Exh Hk Unit Pf mem of eig  4ecd2e63b290: P2 M Companion Theory Rg Exh Hk Unit Pf mem of eig  4ecd2e63b290
-- statement:
--   The P2 M Companion Theory Rg Exh Hk Unit Pf mem of eig  4ecd2e63b290 construction uses the P2 M Companion Theory Rg Exh Hk Unit Pf mem of eig  4ecd2e63b290 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/HeckeUnitTensors/RightCasimirMemSubmodule.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/HeckeUnitTensors/RightCasimirMemSubmodule.lean#L15-L17

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_CommuteLeftRightCasimir
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_RightCasimirMemSubmodule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open CompanionTheory CompanionTheory.RgExh CompanionTheory.RgExh.Hk CompanionTheory.RgExh.Hk.UnitPf
open Formalism.REAL (qdet GlRel)
open Formalism.QuantumDeterminants (capP)
open CompanionTheory.RgExh
variable {m : ℕ} {X : GMod (m + 1)} {χ : Fin (m + 1) → ℂ} {s : Fin (m + 1)}

theorem P2M_CompanionTheory_RgExh_Hk_UnitPf_mem_of_eig__4ecd2e63b290 {M : Type*} [AddCommGroup M] [Module ℂ M] {T : Module.End ℂ M} {μ : ℂ} {f : M}
    (h : T f = μ • f) : f ∈ T.maxGenEigenspace μ := by sorry

alias «CompanionTheory».«RgExh».«Hk».«UnitPf».«mem_of_eig'» := P2M_CompanionTheory_RgExh_Hk_UnitPf_mem_of_eig__4ecd2e63b290
