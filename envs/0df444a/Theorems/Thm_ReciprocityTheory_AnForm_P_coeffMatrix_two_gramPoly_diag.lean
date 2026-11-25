-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_P_coeffMatrix_two_gramPoly_diag
-- name    : ReciprocityTheory.AnForm.P.coeffMatrix_two_gramPoly_diag
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:32:49.585268+00:00
-- url     : https://prove2.me/theorems/38f2e900-502e-4e8c-a919-c98ec669c131
-- title:
--   P: coeff Matrix two gram Poly diag
-- statement:
--   The P construction uses the coeff Matrix two gram Poly diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensB.lean#L129-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensB.lean#L129-L140

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

theorem ReciprocityTheory.AnForm.P.coeffMatrix_two_gramPoly_diag (N : ℕ) (hd : Fin N → ℝ) (v : Pairs N → ℂ) (i : Fin N) :
    cf 2 (gP N hd v) i i = ∑ k, star (zMat N v k i) * ((hd k : ℂ) * zMat N v k i) := by sorry
