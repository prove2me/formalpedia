-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_gen
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.HasGen.gen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:09.655978+00:00
-- url     : https://prove2.me/theorems/e7498974-e5a3-4122-b4d2-cac6fa639bff
-- title:
--   Has Gen: gen
-- statement:
--   The Has Gen construction uses the gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/HasGen.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/HasGen.lean#L24-L28

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}} (L : LB X)
variable {L}

theorem ReciprocityTheory.ChartRestriction.G.DVR.HasGen.gen (hL : L.IsLB) {F : (Y ⟶ X) →₀ ℤ} (h : HasGen L F) {K' : Type} [Fintype K']
    (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (hF : fsum φ' ε' = F) : ∃ g : LB.Gen (LB.LinComb L φ' ε'), g.IsGen := by sorry
