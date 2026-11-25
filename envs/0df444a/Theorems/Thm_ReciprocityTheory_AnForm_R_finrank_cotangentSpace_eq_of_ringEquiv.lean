-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_finrank_cotangentSpace_eq_of_ringEquiv
-- name    : ReciprocityTheory.AnForm.R.finrank_cotangentSpace_eq_of_ringEquiv
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:02:53.884266+00:00
-- url     : https://prove2.me/theorems/e93ad8f0-417c-4b95-9756-fb33a1d43690
-- title:
--   R: finrank cotangent Space eq of ring Equiv
-- statement:
--   The R construction uses the finrank cotangent Space eq of ring Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/LocTransfer.lean#L80-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/LocTransfer.lean#L80-L139

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_LocTransfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial IsLocalRing
noncomputable section
variable {σ : Type} [Fintype σ]

theorem ReciprocityTheory.AnForm.R.finrank_cotangentSpace_eq_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B] (f : A ≃+* B) :
    Module.finrank (ResidueField A) (CotangentSpace A) =
      Module.finrank (ResidueField B) (CotangentSpace B) := by sorry
