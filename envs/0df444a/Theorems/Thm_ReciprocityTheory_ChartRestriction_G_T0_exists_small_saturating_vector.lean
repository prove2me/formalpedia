-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_exists_small_saturating_vector
-- name    : ReciprocityTheory.ChartRestriction.G.T0.exists_small_saturating_vector
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:39:12.258959+00:00
-- url     : https://prove2.me/theorems/26c07719-a8a3-4f8b-909f-4689e2b1d232
-- title:
--   T0: exists small saturating vector
-- statement:
--   The T0 construction uses the exists small saturating vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ExistsSmallSaturatingVector.lean#L131-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ExistsSmallSaturatingVector.lean#L131-L272

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SingleMemStandardLattice
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsNeZeroMemNormSqLeGramDetDivRelIndex
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsSmallSaturatingVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Matrix NumberField
open scoped ComplexOrder

theorem ReciprocityTheory.ChartRestriction.G.T0.exists_small_saturating_vector (K : Type) [Field K] [NumberField K] (r k : ℕ) (b : Fin k → Fin r → K)
    (hb : LinearIndependent K b) (hbL : ∀ j, b j ∈ hStd K r) (hk : k < r) :
    ∃ q : Fin r → 𝓞 K, (fun i => (q i : K)) ∉ Submodule.span K (Set.range b) ∧
      meanK (fun σ => Real.log (hQdist σ b (fun i => (q i : K)))) ≤
        ReciprocityTheory.MultiplicativeHeights.latDeg (fun _ => 1) (ReciprocityTheory.MultiplicativeHeights.satSub (hStd K r) b) b /
            ((Module.finrank ℚ K : ℝ) * ((r - k : ℕ) : ℝ)) +
          1 / 2 * Real.log ((r - k : ℕ) : ℝ) +
          1 / 2 * Real.log (|(NumberField.discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ))) := by sorry
