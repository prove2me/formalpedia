-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_DimF_height_mvPolynomial_fin_of_isMaximal
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.DimF.height_mvPolynomial_fin_of_isMaximal
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:22:41.048786+00:00
-- url     : https://prove2.me/theorems/589f2f2f-7403-56a6-b4b0-29c13b115d48
-- title:
--   Dim F: height mv Polynomial fin of is Maximal
-- statement:
--   The Dim F construction uses the height mv Polynomial fin of is Maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSuppAC.lean#L19-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSuppAC.lean#L19-L33

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.DimF
open Ideal

theorem ReciprocityTheory.ChartRestriction.G.Geo.DimF.height_mvPolynomial_fin_of_isMaximal {k : Type*} [Field k] :
    ∀ (n : ℕ) (M : Ideal (MvPolynomial (Fin n) k)), M.IsMaximal → M.height = n
  := by sorry
