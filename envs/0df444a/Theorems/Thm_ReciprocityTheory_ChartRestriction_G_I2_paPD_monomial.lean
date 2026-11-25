-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paPD_monomial
-- name    : ReciprocityTheory.ChartRestriction.G.I2.paPD_monomial
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:29:52.591743+00:00
-- url     : https://prove2.me/theorems/59368eed-f432-444d-b409-ecface5dddc4
-- title:
--   I2: pa PD monomial
-- statement:
--   The I2 construction uses the pa PD monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAA.lean#L415-L451
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAA.lean#L415-L451

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CardSupportLeAndSumTwoPowLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical

theorem ReciprocityTheory.ChartRestriction.G.I2.paPD_monomial (n : ℕ) : ∀ (m : Fin n → ι) (β : ι →₀ ℕ) (a : ℂ),
    MvPolynomial.constantCoeff (paPD n m (MvPolynomial.monomial β a)) =
      if Finsupp.toMultiset β = (List.ofFn m : Multiset ι) then a * paFact β else 0 := by sorry
