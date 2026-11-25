-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_MHF_bw_add
-- name    : ReciprocityTheory.ChartRestriction.G.T0.MHF.bw_add
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:37:21.613522+00:00
-- url     : https://prove2.me/theorems/5fcc7880-e014-4772-b10b-d413aa3268de
-- title:
--   MHF: bw add
-- statement:
--   The MHF construction uses the bw add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/CoeffPsiBNeZero.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/CoeffPsiBNeZero.lean#L11-L12

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

theorem ReciprocityTheory.ChartRestriction.G.T0.MHF.bw_add (b : Fin B) (s t : Fin B × Fin n →₀ ℕ) : bw b (s + t) = bw b s + bw b t := by sorry
