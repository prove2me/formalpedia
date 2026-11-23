-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_lead_unitary_diag
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.lead_unitary_diag
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:06:44.23638+00:00
-- url     : https://prove2.me/theorems/de42374f-aa86-4255-aa0a-77142cbe4c3e
-- title:
--   S7: lead unitary diag
-- statement:
--   The S7 construction uses the lead unitary diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CBinet.lean#L112-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CBinet.lean#L112-L141

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_Lemmata_GeneralBFact_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CBinet
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

theorem ReciprocityTheory.ChartRestriction.DS.S7.lead_unitary_diag {U : Matrix (Fin n) (Fin n) ℂ} (d : Fin n → ℂ) (i : ℕ) (hi : i ≤ n) :
    lead i (U * Matrix.diagonal d * Uᴴ) =
      ∑ J : {J : Finset (Fin n) // J.card = i},
        ((‖(U.submatrix (Fin.castLE hi) (J.1.orderEmbOfFin J.2)).det‖ ^ 2 : ℝ) : ℂ) * ∏ j ∈ J.1, d j := by sorry
