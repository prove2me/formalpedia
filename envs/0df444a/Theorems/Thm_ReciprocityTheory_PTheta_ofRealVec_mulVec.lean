-- Prove2me | Theorems.Thm_ReciprocityTheory_PTheta_ofRealVec_mulVec
-- name    : ReciprocityTheory.PTheta.ofRealVec_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:33:12.58893+00:00
-- url     : https://prove2.me/theorems/b0a446a1-7b4b-43bd-ae37-e6ebcfc4955d
-- title:
--   PTheta: of Real Vec mul Vec
-- statement:
--   The PTheta construction uses the of Real Vec mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/Change.lean#L66-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/Change.lean#L66-L69

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

theorem ReciprocityTheory.PTheta.ofRealVec_mulVec (M : Matrix ι ι ℤ) (a : ι → ℝ) :
    ofRealVec (M.map (fun x : ℤ => (x : ℝ)) *ᵥ a) = M.map (fun x : ℤ => (x : ℂ)) *ᵥ ofRealVec a := by sorry
