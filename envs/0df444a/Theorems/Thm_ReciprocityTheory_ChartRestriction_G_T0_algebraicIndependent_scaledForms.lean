-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_algebraicIndependent_scaledForms
-- name    : ReciprocityTheory.ChartRestriction.G.T0.algebraicIndependent_scaledForms
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:37:35.733983+00:00
-- url     : https://prove2.me/theorems/fb098a3a-c138-43a9-a2e7-1e017cff3a75
-- title:
--   T0: algebraic Independent scaled Forms
-- statement:
--   The T0 construction uses the algebraic Independent scaled Forms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/AlgebraicIndependentScaledForms.lean#L11-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/AlgebraicIndependentScaledForms.lean#L11-L120

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AevalElimEqRenameLinearSubstitution
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsDualDerivations
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_AlgStep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraicIndependentScaledForms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
open MvPolynomial ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence

theorem ReciprocityTheory.ChartRestriction.G.T0.algebraicIndependent_scaledForms {K Ω : Type} [Field K] [CharZero K] [Field Ω] [Algebra K Ω] {D N : ℕ}
    (y : Fin (N + 1) → Ω) (jc : Fin (N + 1)) (hy : y jc = 1)
    (J : Fin D → Fin N) (δ : Fin D → Derivation K Ω Ω)
    (hδ : ∀ a b, δ a (y (jc.succAbove (J b))) = if a = b then 1 else 0)
    (ρ : Option (Fin D) → Fin (D + 2)) (hρ : Function.Injective ρ) :
    AlgebraicIndependent K (Sum.elim
      (fun p : Fin (D + 2) × Fin (N + 1) =>
        (X (some p) : MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω))
      (fun o : Option (Fin D) => X none * ∑ j, X (some (ρ o, j)) * C (y j))) := by sorry
