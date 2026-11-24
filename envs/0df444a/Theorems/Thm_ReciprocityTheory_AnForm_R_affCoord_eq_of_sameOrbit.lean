-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_affCoord_eq_of_sameOrbit
-- name    : ReciprocityTheory.AnForm.R.affCoord_eq_of_sameOrbit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:48.61172+00:00
-- url     : https://prove2.me/theorems/accf5bda-d8c8-43b8-b949-89ea24fb9c1b
-- title:
--   R: aff Coord eq of same Orbit
-- statement:
--   The R construction uses the aff Coord eq of same Orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/MemConePtsIffChartIdeal.lean#L123-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/MemConePtsIffChartIdeal.lean#L123-L128

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemConePtsIffChartIdeal
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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.AnForm.R.affCoord_eq_of_sameOrbit (p : (k : K) → ι k) {z z' : (Σ k, ι k) → ℂ}
    (h : SameOrbit z z') : affCoord p z = affCoord p z' := by sorry
