-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_P_conjTranspose_mul_diagonal_mul_diag
-- name    : ReciprocityTheory.AnForm.P.conjTranspose_mul_diagonal_mul_diag
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:52:11.803544+00:00
-- url     : https://prove2.me/theorems/4325190d-1b93-4e16-b6c3-c366d202184f
-- title:
--   P: conj Transpose mul diagonal mul diag
-- statement:
--   The P construction uses the conj Transpose mul diagonal mul diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensB.lean#L244-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensB.lean#L244-L251

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

theorem ReciprocityTheory.AnForm.P.conjTranspose_mul_diagonal_mul_diag (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) (a : Fin m) :
    ((Zm N m hm v)ᴴ * (diagonal fun a => (hd (Fin.castLE hm a) : ℂ)) * Zm N m hm v) a a =
      ∑ b : Fin m, star (zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) *
        ((hd (Fin.castLE hm b) : ℂ) * zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) := by sorry
