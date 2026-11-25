-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_polyIn_substitution_leading
-- name    : ReciprocityTheory.ChartRestriction.G.T0.polyIn_substitution_leading
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:40:47.298286+00:00
-- url     : https://prove2.me/theorems/f33882fb-f6a4-4fed-a413-2d6b9d64da6c
-- title:
--   T0: poly In substitution leading
-- statement:
--   The T0 construction uses the poly In substitution leading property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/LogHeightLeTorusHeightSubst.lean#L111-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/LogHeightLeTorusHeightSubst.lean#L111-L167

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

theorem ReciprocityTheory.ChartRestriction.G.T0.polyIn_substitution_leading {D N : ℕ} (f : KTp K D N) (a : Fin (D + 1) → ℕ)
    (hmh : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous a f) :
    (asPolyInVar (Sum.inr 0) (bilinearSubstitution f)).natDegree ≤ ∑ b, a b ∧
      (asPolyInVar (Sum.inr 0) (bilinearSubstitution f)).coeff (∑ b, a b) =
        MvPolynomial.rename (fun t : TVar D N =>
          (Sum.inl (t.1.succ, t.2) : (Fin (D + 2) × Fin (N + 1)) ⊕ Fin (D + 2))) f := by sorry
