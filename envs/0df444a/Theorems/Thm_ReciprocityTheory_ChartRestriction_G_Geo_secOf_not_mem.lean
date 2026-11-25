-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_secOf_not_mem
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.secOf_not_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:30:54.827407+00:00
-- url     : https://prove2.me/theorems/248229eb-5807-5e78-922e-377430b49f1e
-- title:
--   Geo: sec Of not mem
-- statement:
--   The Geo construction uses the sec Of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRedG.lean#L39-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRedG.lean#L39-L44

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial ReciprocityTheory.AnForm.M
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.Geo.secOf_not_mem {P : Ideal (MRing ι)} (hP : P.IsPrime) {i : ∀ k, ι k}
    (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι) ∉ P) (b : K → ℕ) : secOf i b ∉ P := by sorry
