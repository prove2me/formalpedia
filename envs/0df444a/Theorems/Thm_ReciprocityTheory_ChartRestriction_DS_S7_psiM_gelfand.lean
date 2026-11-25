-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_psiM_gelfand
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.psiM_gelfand
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:09:55.701368+00:00
-- url     : https://prove2.me/theorems/4e86b7bd-f00b-417e-b32f-b3e9d58da060
-- title:
--   S7: psi M gelfand
-- statement:
--   The S7 construction uses the psi M gelfand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/GelfandG.lean#L78-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/GelfandG.lean#L78-L116

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_LholClmEventually
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandG
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
variable {ε : Fin n → Bool} {lam : Fin n → ℝ}

theorem ReciprocityTheory.ChartRestriction.DS.S7.psiM_gelfand (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hμ : IsMu lam μ) (k : ℕ)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    opGelfand (rightE ε) k (PsiM T μ) g = gval (icShift lam) k • PsiM T μ g ∧
      opGelfand (rightEanti ε) k (PsiM T μ) g = gval (icShift (-lam)) k • PsiM T μ g := by sorry
