-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InfKH_lowMinusUp_expand
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.InfKH.lowMinusUp_expand
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:46:14.351748+00:00
-- url     : https://prove2.me/theorems/f134c085-5b69-4047-a40f-0c313075d03e
-- title:
--   Inf KH: low Minus Up expand
-- statement:
--   The Inf KH construction uses the low Minus Up expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/LowMinusUpExpand.lean#L29-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/LowMinusUpExpand.lean#L29-L68

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiPart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_TauPart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ByParts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_RhoEqRhoCAddRhoN
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_LowMinusUpExpand
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
open ReciprocityTheory.ChartRestriction.DS.S7.InfKH
variable {Λ : Fin n → ℝ}

theorem ReciprocityTheory.ChartRestriction.DS.S7.InfKH.lowMinusUp_expand {B : Matrix (Fin n) (Fin n) ℂ} (hB : IsBlock ε B) :
    lowMinusUp B = ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a ∧ b ≠ a),
      ((if b < a then (1 : ℂ) else -1) * B a b) • Matrix.single a b (1 : ℂ) := by sorry
