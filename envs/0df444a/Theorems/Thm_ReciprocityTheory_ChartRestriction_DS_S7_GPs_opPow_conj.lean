-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_opPow_conj
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.GPs.opPow_conj
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:46:59.664027+00:00
-- url     : https://prove2.me/theorems/95346751-de19-5a28-baae-f382c6410469
-- title:
--   GPs: op Pow conj
-- statement:
--   The GPs construction uses the op Pow conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/GelfandPsA.lean#L217-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/GelfandPsA.lean#L217-L231

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

theorem ReciprocityTheory.ChartRestriction.DS.S7.GPs.opPow_conj (M : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ) (A B : Matrix (Fin n) (Fin n) ℂ)
    (hAB : A * B = 1) (hBA : B * A = 1) (f : Matrix (Fin n) (Fin n) ℂ → E) (m : ℕ) (a b : Fin n) :
    opPow (fun a b => Lhol (M a b)) m a b (fun y => f (A * y * B)) =
      fun y => opPow (fun a b => Lhol (A * M a b * B)) m a b f (A * y * B) := by sorry
