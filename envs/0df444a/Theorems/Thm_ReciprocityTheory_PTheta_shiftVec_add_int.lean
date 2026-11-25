-- Prove2me | Theorems.Thm_ReciprocityTheory_PTheta_shiftVec_add_int
-- name    : ReciprocityTheory.PTheta.shiftVec_add_int
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:09:24.371673+00:00
-- url     : https://prove2.me/theorems/a9a09b67-7dfb-4203-8bff-533d993a0032
-- title:
--   PTheta: shift Vec add int
-- statement:
--   The PTheta construction uses the shift Vec add int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/Transl.lean#L60-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/Transl.lean#L60-L64

import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
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

theorem ReciprocityTheory.PTheta.shiftVec_add_int (a : ι → ℝ) (l n : ι → ℤ) :
    shiftVec (a + fun i => (n i : ℝ)) l = shiftVec a (l + n) := by sorry
