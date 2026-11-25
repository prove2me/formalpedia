-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_secOf_eq
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.secOf_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:26:59.709926+00:00
-- url     : https://prove2.me/theorems/e9032710-196f-413b-87e6-9408c4ac15e8
-- title:
--   Geo: sec Of eq
-- statement:
--   The Geo construction uses the sec Of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRedG.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRedG.lean#L24-L27

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.secOf_eq (i : ∀ k, ι k) (b : K → ℕ) :
    secOf i b = monomial (∑ k, Finsupp.single (⟨k, i k⟩ : Σ k, ι k) (b k)) 1 := by sorry
