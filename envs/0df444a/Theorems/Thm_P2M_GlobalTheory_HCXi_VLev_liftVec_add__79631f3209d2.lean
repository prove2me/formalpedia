-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HCXi_VLev_liftVec_add__79631f3209d2
-- name    : P2M_GlobalTheory_HCXi_VLev_liftVec_add__79631f3209d2
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:56:33.675399+00:00
-- url     : https://prove2.me/theorems/9f4d0df9-7909-44c1-a4e8-604e1118dfad
-- title:
--   P2 M Global Theory HCXi VLev lift Vec add  79631f3209d2: P2 M Global Theory HCXi VLev lift Vec add  79631f3209d2
-- statement:
--   The P2 M Global Theory HCXi VLev lift Vec add  79631f3209d2 construction uses the P2 M Global Theory HCXi VLev lift Vec add  79631f3209d2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/HalfVolumeLeviRecursion.lean#L76-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/HalfVolumeLeviRecursion.lean#L76-L78

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

theorem P2M_GlobalTheory_HCXi_VLev_liftVec_add__79631f3209d2 (k i r' : ℕ) (v w : Fin (2 * r' + k + 1) → ℂ) :
    liftVec k i r' (v + w) = liftVec k i r' v + liftVec k i r' w := by sorry

alias «GlobalTheory».«HCXi».«VLev».«liftVec_add'» := P2M_GlobalTheory_HCXi_VLev_liftVec_add__79631f3209d2
