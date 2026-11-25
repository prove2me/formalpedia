-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HCXi_VLev_liftVec_smul__cdca075b6107
-- name    : P2M_GlobalTheory_HCXi_VLev_liftVec_smul__cdca075b6107
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:56:43.464056+00:00
-- url     : https://prove2.me/theorems/023ab249-6d75-49da-8b0f-4f2276061497
-- title:
--   P2 M Global Theory HCXi VLev lift Vec smul  cdca075b6107: P2 M Global Theory HCXi VLev lift Vec smul  cdca075b6107
-- statement:
--   The P2 M Global Theory HCXi VLev lift Vec smul  cdca075b6107 construction uses the P2 M Global Theory HCXi VLev lift Vec smul  cdca075b6107 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/HalfVolumeLeviRecursion.lean#L80-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/HalfVolumeLeviRecursion.lean#L80-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_LevelGroupUnitaryHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ParabolicLineStabilizerLeviStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_KsetTransitiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HalfVolumeLeviRecursion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.VLev

theorem P2M_GlobalTheory_HCXi_VLev_liftVec_smul__cdca075b6107 (k i r' : ℕ) (c : ℂ) (v : Fin (2 * r' + k + 1) → ℂ) :
    liftVec k i r' (c • v) = c • liftVec k i r' v := by sorry

alias «GlobalTheory».«HCXi».«VLev».«liftVec_smul'» := P2M_GlobalTheory_HCXi_VLev_liftVec_smul__cdca075b6107
