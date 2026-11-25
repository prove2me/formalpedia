-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_prod_pow_natDegree_coeff
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.prod_pow_natDegree_coeff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:25:17.419098+00:00
-- url     : https://prove2.me/theorems/f96ff1f3-c8b6-476a-95cb-b05061184856
-- title:
--   Geo: prod pow nat Degree coeff
-- statement:
--   The Geo construction uses the prod pow nat Degree coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodD.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodD.lean#L33-L37

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.prod_pow_natDegree_coeff {R ι : Type*} [CommRing R] (s : Finset ι) (p : ι → Polynomial R)
    (e : ι → ℕ) (hp : ∀ i, (p i).natDegree ≤ 1) :
    (∏ i ∈ s, p i ^ e i).natDegree ≤ ∑ i ∈ s, e i ∧
      (∏ i ∈ s, p i ^ e i).coeff (∑ i ∈ s, e i) = ∏ i ∈ s, (p i).coeff 1 ^ e i := by sorry
