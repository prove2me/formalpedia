-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_integral_gReg_eq
-- name    : ReciprocityTheory.AnForm.A.integral_gReg_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:06:26.825871+00:00
-- url     : https://prove2.me/theorems/57d21f69-674d-5ac2-891e-0b20b51c7f7c
-- title:
--   A: integral g Reg eq
-- statement:
--   The A construction uses the integral g Reg eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/HasCompactSupportCompHypInclAt.lean#L16-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/HasCompactSupportCompHypInclAt.lean#L16-L45

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenCoord
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HasCompactSupportCompHypInclAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.AnForm.A.integral_gReg_eq (i : Fin (n + 1)) {U : Set (Fin (n + 1) → ℂ)}
    {v : (Fin (n + 1) → ℂ) → ℝ} {φ : Fin n → (Fin (n + 1) → ℂ) → ℝ} (hp : PoincareLelongData U v φ)
    {ε : ℝ} (hε : 0 < ε) :
    ∫ z, gReg ε (z i) * densV v φ z =
      ∫ z, gReg ε (z i) * maDens (Fin.cons (hDens i v φ) (psiRef n)) z := by sorry
