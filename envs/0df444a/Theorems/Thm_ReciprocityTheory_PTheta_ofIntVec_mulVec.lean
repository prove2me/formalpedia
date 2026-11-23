-- Prove2me | Theorems.Thm_ReciprocityTheory_PTheta_ofIntVec_mulVec
-- name    : ReciprocityTheory.PTheta.ofIntVec_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:16:51.426275+00:00
-- url     : https://prove2.me/theorems/b893b7f5-f341-4721-bce9-8e71c36d8666
-- title:
--   PTheta: of Int Vec mul Vec
-- statement:
--   The PTheta construction uses the of Int Vec mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/Change.lean#L71-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/Change.lean#L71-L74

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

theorem ReciprocityTheory.PTheta.ofIntVec_mulVec (M : Matrix ι ι ℤ) (l : ι → ℤ) :
    ofIntVec (M *ᵥ l) = M.map (fun x : ℤ => (x : ℂ)) *ᵥ ofIntVec l := by sorry
