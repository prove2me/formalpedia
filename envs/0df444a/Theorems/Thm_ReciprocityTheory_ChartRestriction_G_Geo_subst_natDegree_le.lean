-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_subst_natDegree_le
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.subst_natDegree_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:25:21.823514+00:00
-- url     : https://prove2.me/theorems/2dce8611-5462-5698-b7aa-21b2945f6e99
-- title:
--   Geo: subst nat Degree le
-- statement:
--   The Geo construction uses the subst nat Degree le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodD.lean#L51-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodD.lean#L51-L55

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.subst_natDegree_le {r : ℕ} (lam : Fin r → k) (F : MvPolynomial (Fin (r + 1)) k) :
    (subst lam F).natDegree ≤ F.totalDegree := by sorry
