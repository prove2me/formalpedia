-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_comap_extC
-- name    : ReciprocityTheory.AnForm.R.comap_extC
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:42:27.524481+00:00
-- url     : https://prove2.me/theorems/68d41fe4-e35b-5533-b9a8-545c2b7fdb99
-- title:
--   R: comap ext C
-- statement:
--   The R construction uses the comap ext C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExtCContract.lean#L59-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExtCContract.lean#L59-L80

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExtCContract
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
variable {σ : Type} [Fintype σ]

theorem ReciprocityTheory.AnForm.R.comap_extC (I : Ideal (MvPolynomial σ ℚ)) :
    (extC I).comap (MvPolynomial.map (algebraMap ℚ ℂ)) = I := by sorry
