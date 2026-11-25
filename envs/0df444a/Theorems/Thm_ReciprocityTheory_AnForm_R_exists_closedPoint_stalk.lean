-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_exists_closedPoint_stalk
-- name    : ReciprocityTheory.AnForm.R.exists_closedPoint_stalk
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:46:22.556261+00:00
-- url     : https://prove2.me/theorems/3cb399c3-fe04-50b0-9b4c-1f5b8064e05a
-- title:
--   R: exists closed Point stalk
-- statement:
--   The R construction uses the exists closed Point stalk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjHyp.lean#L114-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjHyp.lean#L114-L119

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

theorem ReciprocityTheory.AnForm.R.exists_closedPoint_stalk {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (p : (k : K) → ι k) (x : projX P hP) (hx : x ∈ (chartOpen hP p).1) (hc : IsClosed ({x} : Set (projX P hP))) :
    ∃ y : (Σ k, ι k) → ℂ, (∀ h ∈ chartIdeal P p, eval y h = 0) ∧
      (∀ q, val (toSpecC hP) (chartCoord hP p q) x hx = y q) ∧
      Nonempty ((projX P hP).presheaf.stalk x ≃+* chartLocRing P p y) := by sorry
