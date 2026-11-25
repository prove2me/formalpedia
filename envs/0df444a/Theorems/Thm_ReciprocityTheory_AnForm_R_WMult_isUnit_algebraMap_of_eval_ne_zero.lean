-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_WMult_isUnit_algebraMap_of_eval_ne_zero
-- name    : ReciprocityTheory.AnForm.R.WMult.isUnit_algebraMap_of_eval_ne_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:03:54.694551+00:00
-- url     : https://prove2.me/theorems/a10f6898-9431-56ae-94a8-8557068d04b4
-- title:
--   WMult: is Unit algebra Map of eval ne zero
-- statement:
--   The WMult construction uses the is Unit algebra Map of eval ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WMultB.lean#L21-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WMultB.lean#L21-L27

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WMultA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WMultB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.WMult
open AlgebraicGeometry CategoryTheory MvPolynomial
variable {W : Scheme.{0}} {s : W ⟶ Spec (.of ℂ)}

theorem ReciprocityTheory.AnForm.R.WMult.isUnit_algebraMap_of_eval_ne_zero {n : ℕ} (K : Ideal (MvPolynomial (Fin n) ℂ))
    (p : Fin n → ℂ) {g : MvPolynomial (Fin n) ℂ} (hg : eval p g ≠ 0) :
    IsUnit (algebraMap _ (locRing K p) g) := by sorry
