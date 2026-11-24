-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_subst_coeff_totalDegree
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.subst_coeff_totalDegree
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:58.278827+00:00
-- url     : https://prove2.me/theorems/725b0b35-1a95-4e2b-9ca4-5d90664cf67c
-- title:
--   Geo: subst coeff total Degree
-- statement:
--   The Geo construction uses the subst coeff total Degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodD.lean#L57-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodD.lean#L57-L70

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactMore_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaA_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
variable {k : Type*} [Field k]

theorem ReciprocityTheory.ChartRestriction.G.Geo.subst_coeff_totalDegree {r : ℕ} (lam : Fin r → k) (F : MvPolynomial (Fin (r + 1)) k) :
    (subst lam F).coeff F.totalDegree =
      C (eval (Fin.cons (1 : k) lam) (homogeneousComponent F.totalDegree F)) := by sorry
