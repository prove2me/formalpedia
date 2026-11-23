-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Reg_Transfer_vV_zero__d1cc3821e421
-- name    : P2M_GlobalTheory_Reg_Transfer_vV_zero__d1cc3821e421
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:52:51.474575+00:00
-- url     : https://prove2.me/theorems/2c48825c-7cf9-4d5e-bd65-451f31785b0c
-- title:
--   P2 M Global Theory Reg Transfer v V zero  d1cc3821e421: P2 M Global Theory Reg Transfer v V zero  d1cc3821e421
-- statement:
--   The P2 M Global Theory Reg Transfer v V zero  d1cc3821e421 construction uses the P2 M Global Theory Reg Transfer v V zero  d1cc3821e421 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/RegularAtCentre.lean#L239-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/RegularAtCentre.lean#L239-L241

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_RegularAtCentre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.Transfer
open IsLocalRing Formalism.L2.Pj GlobalTheory.Reg

theorem P2M_GlobalTheory_Reg_Transfer_vV_zero__d1cc3821e421 {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] :
    vV (K' := FractionRing V) V 0 = 0 := by sorry

alias «GlobalTheory».«Reg».«Transfer».«vV_zero'» := P2M_GlobalTheory_Reg_Transfer_vV_zero__d1cc3821e421
