-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hupsTw_coeff_coeff
-- name    : ReciprocityTheory.ChartRestriction.G.T0.hupsTw_coeff_coeff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T05:32:02.870978+00:00
-- url     : https://prove2.me/theorems/f3c9cee4-fc4f-5038-835d-f1f47b778d64
-- title:
--   T0: hups Tw coeff coeff
-- statement:
--   The T0 construction uses the hups Tw coeff coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HupsTwCoeffCoeff.lean#L31-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HupsTwCoeffCoeff.lean#L31-L47

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UpMkApplyInl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HupsTwCoeffCoeff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0

theorem ReciprocityTheory.ChartRestriction.G.T0.hupsTw_coeff_coeff {σ R : Type*} [CommRing R] (w : σ → ℕ) (p : MvPolynomial σ R)
    (j : ℕ) (s : σ →₀ ℕ) :
    ((hupsTw w p).coeff j).coeff s = if hupsWt w s = j then p.coeff s else 0 := by sorry
