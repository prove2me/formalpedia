-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_opPow_Fint
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.GPs.opPow_Fint
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:04:09.25381+00:00
-- url     : https://prove2.me/theorems/23188d61-7bef-4640-98fa-2eb5b8c4a7d9
-- title:
--   GPs: op Pow Fint
-- statement:
--   The GPs construction uses the op Pow Fint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/GelfandPsB.lean#L303-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/GelfandPsB.lean#L303-L319

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
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ} [CompactSpace (KG ε)]

theorem ReciprocityTheory.ChartRestriction.DS.S7.GPs.opPow_Fint (T : KType ε Λ) (M : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ)
    (hg : ContDiffOn ℂ ∞ g (Wset n)) (m : ℕ) : ∀ a b, ∀ z ∈ Ps1.Uset ε,
      opPow (fun a b => Lhol (M a b)) m a b (Fint T g) z = Fint T (opPow (fun a b => DH (M a b)) m a b g) z := by sorry
