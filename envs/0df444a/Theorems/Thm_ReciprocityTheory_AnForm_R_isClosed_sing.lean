-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_isClosed_sing
-- name    : ReciprocityTheory.AnForm.R.isClosed_sing
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:40:51.995919+00:00
-- url     : https://prove2.me/theorems/a4374473-0e06-57b7-ab78-7516a24c01a7
-- title:
--   R: is Closed sing
-- statement:
--   The R construction uses the is Closed sing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjHyp.lean#L121-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjHyp.lean#L121-L125

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehom
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_LogResStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinTypeQE
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypStalk
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypB
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial AlgebraicGeometry CategoryTheory
noncomputable section
variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.AnForm.R.isClosed_sing {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (hQE : FinalTheorems.FinTypeQE) : IsClosed (FinalTheorems.Sing (projX P hP)) := by sorry
