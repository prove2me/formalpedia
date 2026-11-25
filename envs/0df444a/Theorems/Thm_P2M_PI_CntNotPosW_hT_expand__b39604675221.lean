-- Prove2me | Theorems.Thm_P2M_PI_CntNotPosW_hT_expand__b39604675221
-- name    : P2M_PI_CntNotPosW_hT_expand__b39604675221
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:55:57.422419+00:00
-- url     : https://prove2.me/theorems/179b6538-4cb3-4062-92b1-bb83768e11ca
-- title:
--   P2 M PI Cnt Not Pos W h T expand  b39604675221: P2 M PI Cnt Not Pos W h T expand  b39604675221
-- statement:
--   The P2 M PI Cnt Not Pos W h T expand  b39604675221 construction uses the P2 M PI Cnt Not Pos W h T expand  b39604675221 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountPositivity/CardLeOfNegFamily.lean#L13-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountPositivity/CardLeOfNegFamily.lean#L13-L23

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureConjugationInvariant
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountPositivity_CardLeOfNegFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.CntNotPosW
open Matrix
variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem P2M_PI_CntNotPosW_hT_expand__b39604675221 (S : Formalism.BasicNotions.HSpace E) (x y : S.V) :
    S.hT x y = ∑ a, ∑ b, star (S.frame.repr x a) * S.gram a b * S.frame.repr y b := by sorry

alias «PI».«CntNotPosW».«hT_expand'» := P2M_PI_CntNotPosW_hT_expand__b39604675221
