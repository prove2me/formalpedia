-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_I2_IsU_zero__c975529e773e
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_I2_IsU_zero__c975529e773e
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:17:03.032894+00:00
-- url     : https://prove2.me/theorems/c0469533-9db8-5bb8-8ba4-ce4ed8e8ad7c
-- title:
--   P2 M Reciprocity Theory Chart Restriction G I2 Is U zero  c975529e773e: P2 M Reciprocity Theory Chart Restriction G I2 Is U zero  c975529e773e
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G I2 Is U zero  c975529e773e construction uses the P2 M Reciprocity Theory Chart Restriction G I2 Is U zero  c975529e773e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitU.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitU.lean#L24-L25

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_TransferenceMinima
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitU
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
open scoped InnerProductSpace
noncomputable section
variable {E : Type} [Field E] [NumberField E]
variable {dim : (E →+* ℂ) → ℕ}

theorem P2M_ReciprocityTheory_ChartRestriction_G_I2_IsU_zero__c975529e773e (I : Submodule ℤ (Vsp dim)) : IsU I 0 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«I2».«IsU».«zero'» := P2M_ReciprocityTheory_ChartRestriction_G_I2_IsU_zero__c975529e773e
