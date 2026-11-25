-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_coeff_prod_pow_linear
-- name    : ReciprocityTheory.ChartRestriction.G.T0.coeff_prod_pow_linear
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:41:06.98631+00:00
-- url     : https://prove2.me/theorems/33299b26-ca37-5f62-805a-6f5ec2f5ba2e
-- title:
--   T0: coeff prod pow linear
-- statement:
--   The T0 construction uses the coeff prod pow linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/LogHeightLeTorusHeightSubst.lean#L105-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/LogHeightLeTorusHeightSubst.lean#L105-L109

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

theorem ReciprocityTheory.ChartRestriction.G.T0.coeff_prod_pow_linear {B : Type*} [CommRing B] {T : Type*} (s : Finset T) (p : T → Polynomial B)
    (e : T → ℕ) (hp : ∀ t, (p t).natDegree ≤ 1) :
    (∏ t ∈ s, p t ^ e t).natDegree ≤ ∑ t ∈ s, e t ∧
      (∏ t ∈ s, p t ^ e t).coeff (∑ t ∈ s, e t) = ∏ t ∈ s, (p t).coeff 1 ^ e t := by sorry
