-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SW_LagRep_ccT_ccT__22e929649a54
-- name    : P2M_GlobalTheory_SW_LagRep_ccT_ccT__22e929649a54
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:09:25.090958+00:00
-- url     : https://prove2.me/theorems/3c09cdb1-36fe-42f0-94b6-fe747a06ca75
-- title:
--   P2 M Global Theory SW Lag Rep cc T cc T  22e929649a54: P2 M Global Theory SW Lag Rep cc T cc T  22e929649a54
-- statement:
--   The P2 M Global Theory SW Lag Rep cc T cc T  22e929649a54 construction uses the P2 M Global Theory SW Lag Rep cc T cc T  22e929649a54 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LinearIndependentMul.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LinearIndependentMul.lean#L48-L50

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

theorem P2M_GlobalTheory_SW_LagRep_ccT_ccT__22e929649a54 {α β : Type} (A : Matrix α β E) : ccT (ccT A) = A := by sorry

alias «GlobalTheory».«SW».«LagRep».«ccT_ccT'» := P2M_GlobalTheory_SW_LagRep_ccT_ccT__22e929649a54
