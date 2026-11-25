-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_isNoetherianRing_gammaChart
-- name    : ReciprocityTheory.AnForm.R.isNoetherianRing_gammaChart
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:08:54.4908+00:00
-- url     : https://prove2.me/theorems/0a46fa33-0ce4-5ff2-96f8-fa4a8d022a5a
-- title:
--   R: is Noetherian Ring gamma Chart
-- statement:
--   The R construction uses the is Noetherian Ring gamma Chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjHypA.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjHypA.lean#L20-L22

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehom
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_LogResStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinTypeQE
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypA
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

theorem ReciprocityTheory.AnForm.R.isNoetherianRing_gammaChart {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (p : (k : K) → ι k) : IsNoetherianRing Γ(projX P hP, (chartOpen hP p).1) := by sorry
