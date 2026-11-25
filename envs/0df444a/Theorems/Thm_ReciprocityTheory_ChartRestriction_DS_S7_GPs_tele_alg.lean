-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_tele_alg
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.GPs.tele_alg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:47:39.038353+00:00
-- url     : https://prove2.me/theorems/f16f5c3d-4729-5228-b256-e7287f22ab8f
-- title:
--   GPs: tele alg
-- statement:
--   The GPs construction uses the tele alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/GelfandPsA.lean#L82-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/GelfandPsA.lean#L82-L118

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

theorem ReciprocityTheory.ChartRestriction.DS.S7.GPs.tele_alg (P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) (T : Fin n → Fin n → Fin n → Fin n → E)
    (a b : Fin n) :
    ∑ e, ∑ c', ∑ d', (P a c' * Q d' e) • ∑ c, ∑ d, (P e c * Q d b) • T c' d' c d =
      ∑ c, ∑ d, (P a c * Q d b) • ∑ e, T c e e d := by sorry
