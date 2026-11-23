-- Prove2me | Theorems.Thm_ReciprocityTheory_PTheta_shiftVec_eq
-- name    : ReciprocityTheory.PTheta.shiftVec_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:33:17.996902+00:00
-- url     : https://prove2.me/theorems/276c6932-6cbd-4596-8ebe-3a96d995895b
-- title:
--   PTheta: shift Vec eq
-- statement:
--   The PTheta construction uses the shift Vec eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/Change.lean#L63-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/Change.lean#L63-L64

import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix
open ReciprocityTheory ReciprocityTheory.PTheta
variable {ι : Type*} [Fintype ι]

theorem ReciprocityTheory.PTheta.shiftVec_eq (a : ι → ℝ) (l : ι → ℤ) : shiftVec a l = ofIntVec l + ofRealVec a := by sorry
