-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_substFun_natDegree
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.substFun_natDegree
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:25:15.568179+00:00
-- url     : https://prove2.me/theorems/cce32701-2c5c-5e1c-ac5b-896da1e90fa9
-- title:
--   Geo: subst Fun nat Degree
-- statement:
--   The Geo construction uses the subst Fun nat Degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodD.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodD.lean#L20-L25

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.substFun_natDegree {r : ℕ} (lam : Fin r → k) (j : Fin (r + 1)) :
    (substFun lam j).natDegree ≤ 1 := by sorry
