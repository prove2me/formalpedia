-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_P_conjTranspose_mul_coeffMatrix_one_diag
-- name    : ReciprocityTheory.AnForm.P.conjTranspose_mul_coeffMatrix_one_diag
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:51:35.666356+00:00
-- url     : https://prove2.me/theorems/94552996-d9e2-4381-84ba-4e363c41c8e4
-- title:
--   P: conj Transpose mul coeff Matrix one diag
-- statement:
--   The P construction uses the conj Transpose mul coeff Matrix one diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensB.lean#L221-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensB.lean#L221-L232

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

theorem ReciprocityTheory.AnForm.P.conjTranspose_mul_coeffMatrix_one_diag (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) (a : Fin m) :
    ((Zm N m hm v)ᴴ * cf 1 (Gm N hd m hm v)) a a =
      ∑ b : Fin m, star (zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) *
        ((hd (Fin.castLE hm b) : ℂ) * zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) := by sorry
