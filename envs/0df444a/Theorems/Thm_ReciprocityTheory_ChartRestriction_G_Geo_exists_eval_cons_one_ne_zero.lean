-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_exists_eval_cons_one_ne_zero
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.exists_eval_cons_one_ne_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:11.175923+00:00
-- url     : https://prove2.me/theorems/82c0eda9-493f-421c-984d-4237e29901bd
-- title:
--   Geo: exists eval cons one ne zero
-- statement:
--   The Geo construction uses the exists eval cons one ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodD.lean#L86-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodD.lean#L86-L106

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.exists_eval_cons_one_ne_zero [Infinite k] {r : ℕ} (H : MvPolynomial (Fin (r + 1)) k)
    (d : ℕ) (hH : ∀ m ∈ H.support, Finsupp.degree m = d) (h0 : H ≠ 0) :
    ∃ lam : Fin r → k, eval (Fin.cons (1 : k) lam) H ≠ 0 := by sorry
