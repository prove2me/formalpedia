-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_FrobField_funEqSetting_sq
-- name    : ReciprocityTheory.ChartRestriction.L1.FrobField.funEqSetting_sq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:43:20.171566+00:00
-- url     : https://prove2.me/theorems/97dcbf10-2eb2-4036-8705-8cbb40b7fe23
-- title:
--   Frob Field: fun Eq Setting sq
-- statement:
--   The Frob Field construction uses the fun Eq Setting sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgFinA.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgFinA.lean#L14-L16

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffOneSubstOfConstantCoeffEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_SemilinNormPowSubPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgFinA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

theorem ReciprocityTheory.ChartRestriction.L1.FrobField.funEqSetting_sq [CompleteSpace K] (h : FrobField K l σ) :
    FunctionalEquationSetting K l (l ^ 2) (σ.comp σ) := by sorry
