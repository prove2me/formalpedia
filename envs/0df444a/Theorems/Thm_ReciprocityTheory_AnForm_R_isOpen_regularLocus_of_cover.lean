-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_isOpen_regularLocus_of_cover
-- name    : ReciprocityTheory.AnForm.R.isOpen_regularLocus_of_cover
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:13:50.808895+00:00
-- url     : https://prove2.me/theorems/c8595df0-12d5-5091-b677-aadcb10b6f89
-- title:
--   R: is Open regular Locus of cover
-- statement:
--   The R construction uses the is Open regular Locus of cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjHypA.lean#L63-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjHypA.lean#L63-L82

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

theorem ReciprocityTheory.AnForm.R.isOpen_regularLocus_of_cover {X : Scheme.{0}} {J : Type} (U : J → X.affineOpens)
    (hcov : ∀ x, ∃ i, x ∈ (U i).1)
    (h : ∀ i, IsOpen {Q : PrimeSpectrum Γ(X, (U i).1) |
      IsRegularLocalRing (Localization.AtPrime Q.asIdeal)}) :
    IsOpen {x : X | IsRegularLocalRing (X.presheaf.stalk x)} := by sorry
