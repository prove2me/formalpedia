-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_subst_monomial
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.subst_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:08:26.084944+00:00
-- url     : https://prove2.me/theorems/551ef929-ecc3-4db2-bf50-c21dd78d0558
-- title:
--   Geo: subst monomial
-- statement:
--   The Geo construction uses the subst monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodD.lean#L39-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodD.lean#L39-L49

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.subst_monomial {r : ℕ} (lam : Fin r → k) (m : Fin (r + 1) →₀ ℕ) (a : k) :
    (subst lam (monomial m a)).natDegree ≤ Finsupp.degree m ∧
      (subst lam (monomial m a)).coeff (Finsupp.degree m) =
        C (eval (Fin.cons (1 : k) lam) (monomial m a)) := by sorry
