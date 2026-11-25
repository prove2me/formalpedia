-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_exists_holo_coords
-- name    : ReciprocityTheory.AnForm.R.exists_holo_coords
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:37:49.728581+00:00
-- url     : https://prove2.me/theorems/e34597b2-b91c-5e16-a9d2-a2b11c1c8b8b
-- title:
--   R: exists holo coords
-- statement:
--   The R construction uses the exists holo coords property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/AnChart.lean#L19-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/AnChart.lean#L19-L117

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_AnChartA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_AnChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.AnForm.R.exists_holo_coords (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) (e : ℕ)
    [IsRegularLocalRing (locRing K p)] (he : ringKrullDim (locRing K p) = e)
    (r : Fin e → MvPolynomial (Fin n) ℂ)
    (hr : Ideal.span (Set.range fun i => algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) (r i)) =
      Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p)) (ptIdeal p)) :
    ∃ (U : Set (Fin n → ℂ)) (V : Set (Fin e → ℂ)) (g : (Fin e → ℂ) → (Fin n → ℂ)),
      IsOpen U ∧ p ∈ U ∧ IsOpen V ∧ AnalyticOnNhd ℂ g V ∧
      Set.BijOn g V (U ∩ zeroSet K) ∧ ∀ w ∈ V, evalFam r (g w) = w := by sorry
