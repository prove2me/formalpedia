-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_gelfand_Fint
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.GPs.gelfand_Fint
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:06:18.244613+00:00
-- url     : https://prove2.me/theorems/ba374706-f5d7-4a37-bcd1-61b0a425db2b
-- title:
--   GPs: gelfand Fint
-- statement:
--   The GPs construction uses the gelfand Fint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/GelfandPsB.lean#L321-L343
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/GelfandPsB.lean#L321-L343

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

theorem ReciprocityTheory.ChartRestriction.DS.S7.GPs.gelfand_Fint (T : KType ε Λ) (μ : Fin n → ℤ) (M : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ)
    (m : ℕ) (C : ℂ)
    (hM : ∀ (k : KG ε) (z : Matrix (Fin n) (Fin n) ℂ), toMK k⁻¹ * z * toMK k ∈ OmegaSet n →
      opGelfand (fun a b => Lhol (M a b)) m (fun y => PhiM μ (toMK k⁻¹ * y * toMK k)) z =
        C * PhiM μ (toMK k⁻¹ * z * toMK k))
    {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ Ps1.Uset ε) :
    opGelfand (fun a b => Lhol (M a b)) m (psM T μ) z = C • psM T μ z := by sorry
