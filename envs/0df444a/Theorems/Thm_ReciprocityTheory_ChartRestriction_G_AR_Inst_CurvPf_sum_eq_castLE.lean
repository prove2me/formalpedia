-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_sum_eq_castLE
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.sum_eq_castLE
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:03:43.164817+00:00
-- url     : https://prove2.me/theorems/8b4d6e88-9ae9-4901-a4da-0d2aae88e320
-- title:
--   Curv Pf: sum eq cast LE
-- statement:
--   The Curv Pf construction uses the sum eq cast LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/LminorMapConj.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/LminorMapConj.lean#L16-L24

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_LeviVReLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantNormalForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DetSubUpper
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_KappaStatementHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_LminorMapConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
open Matrix ReciprocityTheory.ChartRestriction.G.FD
variable {r : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.sum_eq_castLE {m : ℕ} (hm : m ≤ r) {M : Type} [AddCommMonoid M] (g : Fin r → M)
    (hg : ∀ k : Fin r, m ≤ (k : ℕ) → g k = 0) :
    ∑ k, g k = ∑ j : Fin m, g (Fin.castLE hm j) := by sorry
