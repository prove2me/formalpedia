-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_finrank_cotangentSpace_locAt
-- name    : ReciprocityTheory.AnForm.R.finrank_cotangentSpace_locAt
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:07:24.460225+00:00
-- url     : https://prove2.me/theorems/96879533-47ec-4916-9235-0b0edb805275
-- title:
--   R: finrank cotangent Space loc At
-- statement:
--   The R construction uses the finrank cotangent Space loc At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ConeChartB.lean#L63-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ConeChartB.lean#L63-L75

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

theorem ReciprocityTheory.AnForm.R.finrank_cotangentSpace_locAt {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ))
    (z : σ → ℂ) [IsLocalRing (locAt I z)] :
    Module.finrank (ResidueField (locAt I z)) (CotangentSpace (locAt I z))
      + Module.finrank ℂ (jacSpanAt I z) = Fintype.card σ := by sorry
