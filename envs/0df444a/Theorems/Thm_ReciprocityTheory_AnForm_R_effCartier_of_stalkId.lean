-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_effCartier_of_stalkId
-- name    : ReciprocityTheory.AnForm.R.effCartier_of_stalkId
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:37:04.930573+00:00
-- url     : https://prove2.me/theorems/925fc890-152e-5ab2-85a5-6da80c7b82b8
-- title:
--   R: eff Cartier of stalk Id
-- statement:
--   The R construction uses the eff Cartier of stalk Id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/DivSheaf.lean#L125-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/DivSheaf.lean#L125-L156

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheafA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory
noncomputable section
universe u

theorem ReciprocityTheory.AnForm.R.effCartier_of_stalkId {W : Scheme.{0}} [IsNoetherian W] (G : W.IdealSheafData)
    (hG : ∀ x : W, ∃ t ∈ nonZeroDivisors (W.presheaf.stalk x), FinalTheorems.stalkId G x = Ideal.span {t}) :
    FinalTheorems.EffCartier G := by sorry
