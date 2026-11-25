-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_toMultiset_letters
-- name    : ReciprocityTheory.ChartRestriction.G.I2.toMultiset_letters
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:34:46.553802+00:00
-- url     : https://prove2.me/theorems/47ee7dfd-ef07-59ec-8762-aa8af020f93f
-- title:
--   I2: to Multiset letters
-- statement:
--   The I2 construction uses the to Multiset letters property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PolyDerivDeterminantPolyTensor.lean#L63-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PolyDerivDeterminantPolyTensor.lean#L63-L75

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

theorem ReciprocityTheory.ChartRestriction.G.I2.toMultiset_letters (T : Choice bs) :
    Finsupp.toMultiset (∑ t : Slot bs, Finsupp.single (letter bs T t) 1) =
      Multiset.map (letter bs T) Finset.univ.val := by sorry
