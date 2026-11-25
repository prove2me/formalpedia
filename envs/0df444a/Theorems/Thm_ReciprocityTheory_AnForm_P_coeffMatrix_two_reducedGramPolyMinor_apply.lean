-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_P_coeffMatrix_two_reducedGramPolyMinor_apply
-- name    : ReciprocityTheory.AnForm.P.coeffMatrix_two_reducedGramPolyMinor_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:32:39.224804+00:00
-- url     : https://prove2.me/theorems/e68788f7-bafe-53a2-8479-ef048de5e218
-- title:
--   P: coeff Matrix two reduced Gram Poly Minor apply
-- statement:
--   The P construction uses the coeff Matrix two reduced Gram Poly Minor apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensB.lean#L253-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensB.lean#L253-L267

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

theorem ReciprocityTheory.AnForm.P.coeffMatrix_two_reducedGramPolyMinor_apply (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) (a : Fin m) :
    cf 2 (Gn N hd m hm v) a a =
      ∑ k, star (zMat N v k (Fin.castLE hm a)) * ((hd k : ℂ) * zMat N v k (Fin.castLE hm a)) -
      ∑ b : Fin m, star (zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) *
        ((hd (Fin.castLE hm b) : ℂ) * zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) := by sorry
