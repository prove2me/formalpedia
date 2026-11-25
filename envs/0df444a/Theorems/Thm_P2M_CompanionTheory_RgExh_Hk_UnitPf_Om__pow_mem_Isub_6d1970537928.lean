-- Prove2me | Theorems.Thm_P2M_CompanionTheory_RgExh_Hk_UnitPf_Om__pow_mem_Isub_6d1970537928
-- name    : P2M_CompanionTheory_RgExh_Hk_UnitPf_Om__pow_mem_Isub_6d1970537928
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T15:04:06.639056+00:00
-- url     : https://prove2.me/theorems/79275b03-45cc-4e8a-a913-489b07e2c97c
-- title:
--   P2 M Companion Theory Rg Exh Hk Unit Pf Om  pow mem Isub 6d1970537928: P2 M Companion Theory Rg Exh Hk Unit Pf Om  pow mem Isub 6d1970537928
-- statement:
--   The P2 M Companion Theory Rg Exh Hk Unit Pf Om  pow mem Isub 6d1970537928 construction uses the P2 M Companion Theory Rg Exh Hk Unit Pf Om  pow mem Isub 6d1970537928 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/HeckeUnitTensors/RightCasimirMemSubmodule.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/HeckeUnitTensors/RightCasimirMemSubmodule.lean#L48-L51

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

theorem P2M_CompanionTheory_RgExh_Hk_UnitPf_Om__pow_mem_Isub_6d1970537928 (k : ℕ) {H} (h : H ∈ Isub X) : (Om' X ^ k) H ∈ Isub X := by sorry

alias «CompanionTheory».«RgExh».«Hk».«UnitPf».«Om'_pow_mem_Isub» := P2M_CompanionTheory_RgExh_Hk_UnitPf_Om__pow_mem_Isub_6d1970537928
