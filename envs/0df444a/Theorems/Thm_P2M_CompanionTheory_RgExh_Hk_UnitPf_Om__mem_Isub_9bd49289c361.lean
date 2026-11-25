-- Prove2me | Theorems.Thm_P2M_CompanionTheory_RgExh_Hk_UnitPf_Om__mem_Isub_9bd49289c361
-- name    : P2M_CompanionTheory_RgExh_Hk_UnitPf_Om__mem_Isub_9bd49289c361
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:04:53.416041+00:00
-- url     : https://prove2.me/theorems/f251d9de-b8af-4502-8db4-932b17883275
-- title:
--   P2 M Companion Theory Rg Exh Hk Unit Pf Om  mem Isub 9bd49289c361: P2 M Companion Theory Rg Exh Hk Unit Pf Om  mem Isub 9bd49289c361
-- statement:
--   The P2 M Companion Theory Rg Exh Hk Unit Pf Om  mem Isub 9bd49289c361 construction uses the P2 M Companion Theory Rg Exh Hk Unit Pf Om  mem Isub 9bd49289c361 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/HeckeUnitTensors/RightCasimirMemSubmodule.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/HeckeUnitTensors/RightCasimirMemSubmodule.lean#L44-L46

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

theorem P2M_CompanionTheory_RgExh_Hk_UnitPf_Om__mem_Isub_9bd49289c361 {H} (h : H ∈ Isub X) : Om' X H ∈ Isub X := by sorry

alias «CompanionTheory».«RgExh».«Hk».«UnitPf».«Om'_mem_Isub» := P2M_CompanionTheory_RgExh_Hk_UnitPf_Om__mem_Isub_9bd49289c361
