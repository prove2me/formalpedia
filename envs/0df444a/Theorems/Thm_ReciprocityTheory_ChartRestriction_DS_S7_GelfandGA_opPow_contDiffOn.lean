-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GelfandGA_opPow_contDiffOn
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.GelfandGA.opPow_contDiffOn
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:47:43.775522+00:00
-- url     : https://prove2.me/theorems/a63dc18b-8c42-5464-a495-fef9d09afe61
-- title:
--   Gelfand GA: op Pow cont Diff On
-- statement:
--   The Gelfand GA construction uses the op Pow cont Diff On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/GelfandGA.lean#L71-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/GelfandGA.lean#L71-L87

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsOfFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandGB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandGA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.GelfandGA
local notation "𝕄" => Fin n → Fin n → ℂ
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem ReciprocityTheory.ChartRestriction.DS.S7.GelfandGA.opPow_contDiffOn {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hU : IsOpen U)
    {F : Matrix (Fin n) (Fin n) ℂ → E} (hF : ContDiffOn ℂ ∞ F U)
    (Y : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ) :
    ∀ j a b, ContDiffOn ℂ ∞ (opPow (fun a b => Lhol (Y a b)) j a b F) U := by sorry
