-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_hasFDerivAt_Fint
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.GPs.hasFDerivAt_Fint
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:59:56.129559+00:00
-- url     : https://prove2.me/theorems/6feb029e-60c8-53db-9509-127d81865287
-- title:
--   GPs: has FDeriv At Fint
-- statement:
--   The GPs construction uses the has FDeriv At Fint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/GelfandPsB.lean#L219-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/GelfandPsB.lean#L219-L236

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsB
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
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.GPs
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
local notation "𝕄f" => Fin n → Fin n → ℂ
variable {g : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → ℂ}
variable [CompactSpace (KG ε)]

theorem ReciprocityTheory.ChartRestriction.DS.S7.GPs.hasFDerivAt_Fint (T : KType ε Λ) (hg : ContDiffOn ℂ ∞ g (Wset n)) {z : Matrix (Fin n) (Fin n) ℂ}
    (hz : z ∈ Ps1.Uset ε) :
    HasFDerivAt (fun x : 𝕄f => Fint T g x) (cK T • ∫ k, FD T g z k ∂(muK ε)) z := by sorry
