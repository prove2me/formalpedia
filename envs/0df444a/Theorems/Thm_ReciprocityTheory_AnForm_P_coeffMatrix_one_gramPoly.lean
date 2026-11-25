-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_P_coeffMatrix_one_gramPoly
-- name    : ReciprocityTheory.AnForm.P.coeffMatrix_one_gramPoly
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:33:03.928919+00:00
-- url     : https://prove2.me/theorems/3110bc61-2d3b-45f8-a28e-804992e5d250
-- title:
--   P: coeff Matrix one gram Poly
-- statement:
--   The P construction uses the coeff Matrix one gram Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensB.lean#L121-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensB.lean#L121-L127

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open Polynomial Matrix
noncomputable section

theorem ReciprocityTheory.AnForm.P.coeffMatrix_one_gramPoly (N : ℕ) (hd : Fin N → ℝ) (v : Pairs N → ℂ) :
    cf 1 (gP N hd v) = (diagonal fun k => (hd k : ℂ)) * zMat N v +
      (zMat N v)ᴴ * diagonal fun k => (hd k : ℂ) := by sorry
