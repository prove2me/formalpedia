-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_MHF_isMH_of_pow
-- name    : ReciprocityTheory.ChartRestriction.G.T0.MHF.isMH_of_pow
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:37:33.39514+00:00
-- url     : https://prove2.me/theorems/ff769167-8993-4b8f-bfd9-18ae3617a9df
-- title:
--   MHF: is MH of pow
-- statement:
--   The MHF construction uses the is MH of pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/CoeffPsiBNeZero.lean#L66-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/CoeffPsiBNeZero.lean#L66-L100

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CoeffPsiBNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.MHF
open MvPolynomial ReciprocityTheory.MultiplicativeHeights
variable {K : Type*} [Field K] {B n : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.T0.MHF.isMH_of_pow (hB : 0 < B) (F0 : MvPolynomial (Fin B × Fin n) K) (κ : K) (m δ : ℕ)
    (hm : 1 ≤ m) (hκ : κ ≠ 0) (hF0 : F0 ≠ 0)
    (h : IsMultiHomogeneous (fun _ => δ) (C κ * F0 ^ m)) :
    ∃ d0, m * d0 = δ ∧ IsMultiHomogeneous (fun _ => d0) F0 := by sorry
