-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isGoodProj_of_intOver
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.isGoodProj_of_intOver
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:24:32.77414+00:00
-- url     : https://prove2.me/theorems/6256ddaf-7691-5ffc-8c2a-33f7ef4da0f7
-- title:
--   Geo: is Good Proj of int Over
-- statement:
--   The Geo construction uses the is Good Proj of int Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivPushC.lean#L26-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivPushC.lean#L26-L72

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivPushA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivPushC
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
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.Geo.isGoodProj_of_intOver {P : Ideal (MRing ι)} (hK : Nonempty K) (hhom : IsMultiHomogIdeal P)
    {e r : ℕ} (hr : r ≤ e + 1) (L : Fin r → ((k : K) → ι k) → ℚ)
    (hL : ∀ t, IntOver ℚ (forms (segQ P) L) (segQ P t)) :
    IsGoodProj P (projOfForms (e := e) L) := by sorry
