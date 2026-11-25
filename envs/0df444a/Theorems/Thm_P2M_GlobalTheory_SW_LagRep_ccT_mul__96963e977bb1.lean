-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SW_LagRep_ccT_mul__96963e977bb1
-- name    : P2M_GlobalTheory_SW_LagRep_ccT_mul__96963e977bb1
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:09:25.904807+00:00
-- url     : https://prove2.me/theorems/91b6e677-09cb-4e90-84de-d85cbdb4217c
-- title:
--   P2 M Global Theory SW Lag Rep cc T mul  96963e977bb1: P2 M Global Theory SW Lag Rep cc T mul  96963e977bb1
-- statement:
--   The P2 M Global Theory SW Lag Rep cc T mul  96963e977bb1 construction uses the P2 M Global Theory SW Lag Rep cc T mul  96963e977bb1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LinearIndependentMul.lean#L52-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LinearIndependentMul.lean#L52-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LinearIndependentMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.LagRep
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem P2M_GlobalTheory_SW_LagRep_ccT_mul__96963e977bb1 {α β δ : Type} [Fintype β] (A : Matrix α β E) (B : Matrix β δ E) :
    ccT (A * B) = ccT B * ccT A := by sorry

alias «GlobalTheory».«SW».«LagRep».«ccT_mul'» := P2M_GlobalTheory_SW_LagRep_ccT_mul__96963e977bb1
