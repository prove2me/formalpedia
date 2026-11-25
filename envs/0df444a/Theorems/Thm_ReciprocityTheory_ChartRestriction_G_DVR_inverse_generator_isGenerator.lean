-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_inverse_generator_isGenerator
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.inverse_generator_isGenerator
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:10:54.863903+00:00
-- url     : https://prove2.me/theorems/790a70f2-224d-46e3-abd7-4e85a09d32a5
-- title:
--   DVR: inverse generator is Generator
-- statement:
--   The DVR construction uses the inverse generator is Generator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBPull.lean#L62-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBPull.lean#L62-L75

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
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

theorem ReciprocityTheory.ChartRestriction.G.DVR.inverse_generator_isGenerator {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (i j : K → L.ι) :
    res (inf_le_left : (LB.LinComb L φ (fun k => -ε k)).U i ⊓ (LB.LinComb L φ (fun k => -ε k)).U j ≤
        (LB.LinComb L φ (fun k => -ε k)).U i) ((LB.invGen L φ ε t).s i) =
      (LB.LinComb L φ (fun k => -ε k)).g i j *
        res (inf_le_right : (LB.LinComb L φ (fun k => -ε k)).U i ⊓ (LB.LinComb L φ (fun k => -ε k)).U j ≤
          (LB.LinComb L φ (fun k => -ε k)).U j) ((LB.invGen L φ ε t).s j) := by sorry
