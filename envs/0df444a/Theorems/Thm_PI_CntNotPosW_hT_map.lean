-- Prove2me | Theorems.Thm_PI_CntNotPosW_hT_map
-- name    : PI.CntNotPosW.hT_map
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:26:28.124995+00:00
-- url     : https://prove2.me/theorems/8053bcd5-d428-4927-933d-f0d83a88ba87
-- title:
--   Cnt Not Pos W: h T map
-- statement:
--   The Cnt Not Pos W construction uses the h T map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountPositivity/CardLeOfNegFamily.lean#L25-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountPositivity/CardLeOfNegFamily.lean#L25-L32

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

theorem PI.CntNotPosW.hT_map (S : Formalism.BasicNotions.HSpace E) (τ : E →+* ℂ) (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a))
    (x y : S.V) :
    τ (S.hT x y) = ∑ a, ∑ b, star (τ (S.frame.repr x a)) * (S.gram.map τ) a b * τ (S.frame.repr y b) := by sorry
