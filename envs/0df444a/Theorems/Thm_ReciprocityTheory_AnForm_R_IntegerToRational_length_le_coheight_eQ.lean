-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_IntegerToRational_length_le_coheight_eQ
-- name    : ReciprocityTheory.AnForm.R.IntegerToRational.length_le_coheight_eQ
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:51:22.887948+00:00
-- url     : https://prove2.me/theorems/8572e388-5d8b-4ba3-bb4e-d599efa0e827
-- title:
--   Integer To Rational: length le coheight e Q
-- statement:
--   The Integer To Rational construction uses the length le coheight e Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/IntToRatB.lean#L29-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/IntToRatB.lean#L29-L50

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IntegerToRational
open MvPolynomial
variable {σ : Type} [Fintype σ]

theorem ReciprocityTheory.AnForm.R.IntegerToRational.length_le_coheight_eQ (s : LTSeries (PrimeSpectrum (MvPolynomial σ ℤ))) :
    ∀ z, s.head = z → ∀ h0 : ChZero z.asIdeal,
      (s.length : ℕ∞) ≤ Order.coheight (eQ z h0) + 1 := by sorry
