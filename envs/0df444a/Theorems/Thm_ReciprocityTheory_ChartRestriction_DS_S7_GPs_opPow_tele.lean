-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_opPow_tele
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.GPs.opPow_tele
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:48:52.674236+00:00
-- url     : https://prove2.me/theorems/df3b2713-1288-5409-adcf-8409af8cbb5b
-- title:
--   GPs: op Pow tele
-- statement:
--   The GPs construction uses the op Pow tele property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/GelfandPsA.lean#L138-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/GelfandPsA.lean#L138-L188

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

theorem ReciprocityTheory.ChartRestriction.DS.S7.GPs.opPow_tele {V : Set (Matrix (Fin n) (Fin n) ℂ)} (hV : IsOpen V)
    (M N : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ) (P Q : Matrix (Fin n) (Fin n) ℂ)
    (hN : ∀ a b, N a b = ∑ c, ∑ d, (P a c * Q d b) • M c d) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : ContDiffOn ℂ ∞ f V) (m : ℕ) :
    ∀ a b, ∀ z ∈ V, opPow (fun a b => Lhol (N a b)) m a b f z =
      ∑ c, ∑ d, (P a c * Q d b) • opPow (fun a b => Lhol (M a b)) m c d f z := by sorry
