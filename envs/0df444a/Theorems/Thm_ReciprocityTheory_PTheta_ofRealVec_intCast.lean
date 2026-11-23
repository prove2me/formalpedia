-- Prove2me | Theorems.Thm_ReciprocityTheory_PTheta_ofRealVec_intCast
-- name    : ReciprocityTheory.PTheta.ofRealVec_intCast
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:33:14.588601+00:00
-- url     : https://prove2.me/theorems/520c3c55-f59f-4dad-813d-90e425d5dc6d
-- title:
--   PTheta: of Real Vec int Cast
-- statement:
--   The PTheta construction uses the of Real Vec int Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/Transl.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/Transl.lean#L44-L46

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

theorem ReciprocityTheory.PTheta.ofRealVec_intCast (n : ι → ℤ) : ofRealVec (fun i => (n i : ℝ)) = ofIntVec n := by sorry
