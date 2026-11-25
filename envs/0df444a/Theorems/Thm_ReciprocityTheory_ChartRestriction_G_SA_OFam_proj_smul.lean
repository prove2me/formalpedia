-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_OFam_proj_smul
-- name    : ReciprocityTheory.ChartRestriction.G.SA.OFam.proj_smul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:33:10.962302+00:00
-- url     : https://prove2.me/theorems/c0e2af6b-6f30-4ccd-8842-6494d1476ad7
-- title:
--   OFam: proj smul
-- statement:
--   The OFam construction uses the proj smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/SubProjOrth.lean#L118-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/SubProjOrth.lean#L118-L125

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SubProjOrth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}
variable {e f : ι → K}

theorem ReciprocityTheory.ChartRestriction.G.SA.OFam.proj_smul {r : ℕ} (F : OFam σ J e f r) (c : K) (x : ι → K) :
    F.proj (c • x) = c • F.proj x := by sorry
