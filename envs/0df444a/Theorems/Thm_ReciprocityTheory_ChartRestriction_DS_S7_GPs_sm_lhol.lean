-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_sm_lhol
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.GPs.sm_lhol
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:47:58.067462+00:00
-- url     : https://prove2.me/theorems/d80264f0-692d-482f-bd54-9acdb3dd46b0
-- title:
--   GPs: sm lhol
-- statement:
--   The GPs construction uses the sm lhol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/GelfandPsA.lean#L60-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/GelfandPsA.lean#L60-L63

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPhi
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.GPs
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem ReciprocityTheory.ChartRestriction.DS.S7.GPs.sm_lhol {V : Set (Matrix (Fin n) (Fin n) ℂ)} (hV : IsOpen V) {f : Matrix (Fin n) (Fin n) ℂ → E}
    (hf : ContDiffOn ℂ ∞ f V) (X : Matrix (Fin n) (Fin n) ℂ) : ContDiffOn ℂ ∞ (Lhol X f) V := by sorry
