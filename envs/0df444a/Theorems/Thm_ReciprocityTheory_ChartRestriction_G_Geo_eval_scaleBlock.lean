-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_eval_scaleBlock
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.eval_scaleBlock
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:16:28.537817+00:00
-- url     : https://prove2.me/theorems/742c4369-b7db-43c3-a2fc-8228f5fe9e34
-- title:
--   Geo: eval scale Block
-- statement:
--   The Geo construction uses the eval scale Block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGood.lean#L15-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGood.lean#L15-L31

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
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

theorem ReciprocityTheory.ChartRestriction.G.Geo.eval_scaleBlock (k0 : K) (c : ℂ) (z : (Σ k, ι k) → ℂ) (f : MRing ι) (a : K → ℕ)
    (hf : IsMultiHomog f a) :
    eval (scaleBlock k0 c z) (map (Int.castRingHom ℂ) f) =
      c ^ a k0 * eval z (map (Int.castRingHom ℂ) f) := by sorry
