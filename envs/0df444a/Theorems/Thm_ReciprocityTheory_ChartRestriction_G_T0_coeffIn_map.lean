-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_coeffIn_map
-- name    : ReciprocityTheory.ChartRestriction.G.T0.coeffIn_map
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:38:28.435073+00:00
-- url     : https://prove2.me/theorems/6ec12970-9b9e-585a-96c7-9c5da4a52ea6
-- title:
--   T0: coeff In map
-- statement:
--   The T0 construction uses the coeff In map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/LogHeightLeTorusHeightSubst.lean#L80-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/LogHeightLeTorusHeightSubst.lean#L80-L87

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AevalElimEqRenameLinearSubstitution
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_LagrangeIdealLiftsFact
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ContinuousTorusPoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NatDegreeLeAndCoeffProdPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LogHeightLeTorusHeightSubst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
variable {R : Type*} [CommRing R] {V : Type*} [DecidableEq V]

theorem ReciprocityTheory.ChartRestriction.G.T0.coeffIn_map {S : Type*} [CommRing S] (φ : R →+* S) (hφ : Function.Injective φ) (i : V)
    (k : ℕ) (P : MvPolynomial V R) :
    ReciprocityTheory.MultiplicativeHeights.coeffIn i k (MvPolynomial.map φ P) =
      MvPolynomial.map φ (ReciprocityTheory.MultiplicativeHeights.coeffIn i k P) := by sorry
