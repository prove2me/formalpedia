-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_MHF_bw_single
-- name    : ReciprocityTheory.ChartRestriction.G.T0.MHF.bw_single
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:37:29.683837+00:00
-- url     : https://prove2.me/theorems/713497e9-549b-4a9e-bd88-f1db40e8ff9f
-- title:
--   MHF: bw single
-- statement:
--   The MHF construction uses the bw single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/CoeffPsiBNeZero.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/CoeffPsiBNeZero.lean#L14-L19

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

theorem ReciprocityTheory.ChartRestriction.G.T0.MHF.bw_single (b : Fin B) (v : Fin B × Fin n) (e : ℕ) :
    bw b (Finsupp.single v e) = if v.1 = b then e else 0 := by sorry
