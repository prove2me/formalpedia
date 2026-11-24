-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inh_pointValue
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.inh_pointValue
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:24.90907+00:00
-- url     : https://prove2.me/theorems/69e03a09-20d3-4d3c-83de-44a71f09b800
-- title:
--   I1: inh point Value
-- statement:
--   The I1 construction uses the inh point Value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/Inhabit.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/Inhabit.lean#L38-L43

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_Inhabit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] [DecidableEq (Σ k, ι k)]
  {F : Type*} [Field F]

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.inh_pointValue {I : IFamily F ι} (hI : IsFieldIntersection I) (S : Finset (Σ k, ι k))
    (i : ∀ k, ι k) (hproj : IsProjVarF (inhV F S) 0)
    (hcov : ∀ s : Σ k, ι k, s ∉ S → s = ⟨s.1, i s.1⟩) (hdisj : ∀ k, (⟨k, i k⟩ : Σ k, ι k) ∉ S)
    (L : Fin 0 → K → ℤ) : I (inhV F S) 0 L = 1 := by sorry
