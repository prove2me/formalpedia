-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_sub_LMU
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.sub_LMU
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:05:40.063578+00:00
-- url     : https://prove2.me/theorems/944e0cba-b229-5e10-83bf-800ea395ccd6
-- title:
--   Curv Pf: sub LMU
-- statement:
--   The Curv Pf construction uses the sub LMU property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/LminorMapConj.lean#L26-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/LminorMapConj.lean#L26-L42

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

theorem ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.sub_LMU {m : ℕ} (hm : m ≤ r) (L M U : Matrix (Fin r) (Fin r) ℂ)
    (hL : ∀ a c : Fin r, c < a → L a c = 0) (hU : ∀ a c : Fin r, c < a → U a c = 0) :
    (Lᵀ * M * U).submatrix (Fin.castLE hm) (Fin.castLE hm) =
      (L.submatrix (Fin.castLE hm) (Fin.castLE hm))ᵀ * M.submatrix (Fin.castLE hm) (Fin.castLE hm) *
        U.submatrix (Fin.castLE hm) (Fin.castLE hm) := by sorry
