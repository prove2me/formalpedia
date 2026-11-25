-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_inv_conj_exp
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.inv_conj_exp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:45:29.445642+00:00
-- url     : https://prove2.me/theorems/3e3f958d-b4c0-4ceb-be04-e80ec4c2fd0d
-- title:
--   S7: inv conj exp
-- statement:
--   The S7 construction uses the inv conj exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/PsiMExpFormula.lean#L16-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/PsiMExpFormula.lean#L16-L27

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ToMKMulInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExistsMu
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiMExpFormula
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool}

theorem ReciprocityTheory.ChartRestriction.DS.S7.inv_conj_exp (k : KG ε) (X : Matrix (Fin n) (Fin n) ℂ) :
    (toMK k⁻¹ * NormedSpace.exp X * toMK k)⁻¹ = toMK k⁻¹ * NormedSpace.exp (-X) * toMK k := by sorry
