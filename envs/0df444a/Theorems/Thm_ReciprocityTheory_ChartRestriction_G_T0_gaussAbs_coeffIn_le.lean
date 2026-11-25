-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_gaussAbs_coeffIn_le
-- name    : ReciprocityTheory.ChartRestriction.G.T0.gaussAbs_coeffIn_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:38:37.716725+00:00
-- url     : https://prove2.me/theorems/7046d4bd-fccd-4878-95e8-d30c72fe26a9
-- title:
--   T0: gauss Abs coeff In le
-- statement:
--   The T0 construction uses the gauss Abs coeff In le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/LogHeightLeTorusHeightSubst.lean#L91-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/LogHeightLeTorusHeightSubst.lean#L91-L103

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

theorem ReciprocityTheory.ChartRestriction.G.T0.gaussAbs_coeffIn_le {V : Type*} (w : FinitePlace K) (i : V) (k : ℕ)
    (P : MvPolynomial V K) :
    ReciprocityTheory.MultiplicativeHeights.gaussAbs w (ReciprocityTheory.MultiplicativeHeights.coeffIn i k P) ≤ ReciprocityTheory.MultiplicativeHeights.gaussAbs w P := by sorry
