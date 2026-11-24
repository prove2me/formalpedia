-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_maximalIdeal_locRing
-- name    : ReciprocityTheory.AnForm.R.maximalIdeal_locRing
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:52:26.920235+00:00
-- url     : https://prove2.me/theorems/8b3dafff-d20d-4c5d-a7af-2e5b661fe2f3
-- title:
--   R: maximal Ideal loc Ring
-- statement:
--   The R construction uses the maximal Ideal loc Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/StalkLocA.lean#L54-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/StalkLocA.lean#L54-L60

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocA
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

theorem ReciprocityTheory.AnForm.R.maximalIdeal_locRing {K : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin n → ℂ}
    (hK : K ≤ ptIdeal p) [IsLocalRing (locRing K p)] :
    IsLocalRing.maximalIdeal (locRing K p) = (ptIdeal p).map (algebraMap _ (locRing K p)) := by sorry
