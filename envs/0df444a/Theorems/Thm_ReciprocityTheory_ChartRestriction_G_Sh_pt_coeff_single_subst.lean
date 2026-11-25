-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_pt_coeff_single_subst
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.pt_coeff_single_subst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:36:44.609024+00:00
-- url     : https://prove2.me/theorems/e7a90e03-989c-4543-bb22-b1904ac7f6dd
-- title:
--   Sh: pt coeff single subst
-- statement:
--   The Sh construction uses the pt coeff single subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtCoeffSingleSubst.lean#L215-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtCoeffSingleSubst.lean#L215-L252

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtOrderProdSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtCoeffSingleSubst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh
open Classical
noncomputable section
variable {R : Type*} [CommRing R]

theorem ReciprocityTheory.ChartRestriction.G.Sh.pt_coeff_single_subst {σ τ : Type*} [Fintype σ]
    {A : σ → MvPowerSeries τ R} (hA : HasSubst A) (hA0 : ∀ s, constantCoeff (A s) = 0)
    {f : MvPowerSeries σ R} (hf : constantCoeff f = 0) (i : τ) :
    coeff (Finsupp.single i 1) (subst A f) =
      ∑ s, coeff (Finsupp.single s 1) f * coeff (Finsupp.single i 1) (A s) := by sorry
