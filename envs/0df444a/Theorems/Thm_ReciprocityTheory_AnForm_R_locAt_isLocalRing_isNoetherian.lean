-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_locAt_isLocalRing_isNoetherian
-- name    : ReciprocityTheory.AnForm.R.locAt_isLocalRing_isNoetherian
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:07:07.919734+00:00
-- url     : https://prove2.me/theorems/5007e50c-eeaa-42af-960b-0a18ed693a3f
-- title:
--   R: loc At is Local Ring is Noetherian
-- statement:
--   The R construction uses the loc At is Local Ring is Noetherian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ConeChartB.lean#L11-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ConeChartB.lean#L11-L25

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_LocTransfer
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartB
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

theorem ReciprocityTheory.AnForm.R.locAt_isLocalRing_isNoetherian {σ : Type} [Finite σ] (I : Ideal (MvPolynomial σ ℂ))
    (z : σ → ℂ) (hz : ∀ h ∈ I, eval z h = 0) :
    IsLocalRing (locAt I z) ∧ IsNoetherianRing (locAt I z) := by sorry
