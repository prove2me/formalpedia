-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_polyDeriv_determinantPoly_tensor
-- name    : ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_determinantPoly_tensor
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:30:52.462847+00:00
-- url     : https://prove2.me/theorems/9106c08c-9e01-5373-9ede-5257f476a30e
-- title:
--   I2: poly Deriv determinant Poly tensor
-- statement:
--   The I2 construction uses the poly Deriv determinant Poly tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PolyDerivDeterminantPolyTensor.lean#L77-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PolyDerivDeterminantPolyTensor.lean#L77-L97

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormFundamentalDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivDeterminantPolyTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MvPolynomial
noncomputable section
variable {E : Type} [Field E] [NumberField E] {n nb : ℕ} {dim : (E →+* ℂ) → ℕ}
variable (X : PT E) (bs : Fin nb → Block E n X.dim)

theorem ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_determinantPoly_tensor (s : Fin n → (Fin 1 → Vsp X.dim) → ℂ)
    (hs : ∀ k, ContDiff ℂ (⊤ : ℕ∞) (s k)) :
    polyDeriv (P1 bs) dir (tens X s) 0 =
      ∑ T : Choice bs, sgnT bs T * ∏ k, d1 (s k) (colL (lst X bs T) k).length
        (fun j => (colL (lst X bs T) k).get j) := by sorry
