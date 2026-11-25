-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_isRegularLocalRing_stalk_fromSpec_iff
-- name    : ReciprocityTheory.AnForm.R.isRegularLocalRing_stalk_fromSpec_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:10:33.099344+00:00
-- url     : https://prove2.me/theorems/997dfaa2-3fc5-4121-850f-71107fb1a282
-- title:
--   R: is Regular Local Ring stalk from Spec iff
-- statement:
--   The R construction uses the is Regular Local Ring stalk from Spec iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjHypA.lean#L51-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjHypA.lean#L51-L61

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

theorem ReciprocityTheory.AnForm.R.isRegularLocalRing_stalk_fromSpec_iff {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
    (y : PrimeSpectrum Γ(X, U)) (hy : hU.fromSpec y ∈ U) :
    IsRegularLocalRing (X.presheaf.stalk (hU.fromSpec y)) ↔
      IsRegularLocalRing (Localization.AtPrime y.asIdeal) := by sorry
