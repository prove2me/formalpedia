-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_substFun_coeff_one
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.substFun_coeff_one
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:25:08.896317+00:00
-- url     : https://prove2.me/theorems/2a1a56ea-60cb-547e-99a3-340a9ccfbe6b
-- title:
--   Geo: subst Fun coeff one
-- statement:
--   The Geo construction uses the subst Fun coeff one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodD.lean#L27-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodD.lean#L27-L31

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.substFun_coeff_one {r : ℕ} (lam : Fin r → k) (j : Fin (r + 1)) :
    (substFun lam j).coeff 1 = C ((Fin.cons (1 : k) lam : Fin (r + 1) → k) j) := by sorry
