-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_lhol_congr
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.GPs.lhol_congr
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:46:52.396879+00:00
-- url     : https://prove2.me/theorems/b1ca82a8-3a96-5af3-bc25-a5be76e6a907
-- title:
--   GPs: lhol congr
-- statement:
--   The GPs construction uses the lhol congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/GelfandPsA.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/GelfandPsA.lean#L28-L32

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPhi
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_lhol_congr

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

theorem ReciprocityTheory.ChartRestriction.DS.S7.GPs.lhol_congr {V : Set (Matrix (Fin n) (Fin n) ℂ)} (hV : IsOpen V) {f g : Matrix (Fin n) (Fin n) ℂ → E}
    (h : Set.EqOn f g V) (X : Matrix (Fin n) (Fin n) ℂ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ V) :
    Lhol X f z = Lhol X g z := by sorry
