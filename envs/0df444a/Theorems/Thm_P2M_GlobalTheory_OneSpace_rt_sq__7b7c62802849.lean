-- Prove2me | Theorems.Thm_P2M_GlobalTheory_OneSpace_rt_sq__7b7c62802849
-- name    : P2M_GlobalTheory_OneSpace_rt_sq__7b7c62802849
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:18:50.051779+00:00
-- url     : https://prove2.me/theorems/93fd3a54-0682-4235-b5ee-605e6679e7d6
-- title:
--   P2 M Global Theory One Space rt sq  7b7c62802849: P2 M Global Theory One Space rt sq  7b7c62802849
-- statement:
--   The P2 M Global Theory One Space rt sq  7b7c62802849 construction uses the P2 M Global Theory One Space rt sq  7b7c62802849 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HermitianFormsSameSignatureSameSpace.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HermitianFormsSameSignatureSameSpace.lean#L22-L24

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetMulVolMulConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHermCoordOfDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SignatureHermitianModelOfDatumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsBinaryEqAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ConjEqNegOfSqEqNegNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermitianFormsSameSignatureSameSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.OneSpace
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem P2M_GlobalTheory_OneSpace_rt_sq__7b7c62802849 (H : Host E) : (H.rt : E) ^ 2 = -(H.d : E) := by sorry

alias «GlobalTheory».«OneSpace».«rt_sq'» := P2M_GlobalTheory_OneSpace_rt_sq__7b7c62802849
