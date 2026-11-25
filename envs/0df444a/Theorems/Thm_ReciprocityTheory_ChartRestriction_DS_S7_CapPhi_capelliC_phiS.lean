-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CapPhi_capelliC_phiS
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.CapPhi.capelliC_phiS
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:45:36.56516+00:00
-- url     : https://prove2.me/theorems/d2575507-40e5-4030-8ac9-23cf75493321
-- title:
--   Cap Phi: capelli C phi S
-- statement:
--   The Cap Phi construction uses the capelli C phi S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CapPhi.lean#L106-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CapPhi.lean#L106-L119

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiCapelliStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPhiA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Central
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CapPhi
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
open ReciprocityTheory.ChartRestriction.DS.S7.CapPhi
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

theorem ReciprocityTheory.ChartRestriction.DS.S7.CapPhi.capelliC_phiS (μ : Fin n → ℤ) (u : ℂ) :
    capelliC (negE (n := n)) u (phiS μ) =
      ((-1) ^ n * ∏ a : Fin n, ((n : ℂ) - 1 - u + -(μ a : ℂ) - ((a : ℕ) : ℂ))) • phiS μ := by sorry
