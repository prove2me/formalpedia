-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_gammaChart_symm_mk
-- name    : ReciprocityTheory.AnForm.R.gammaChart_symm_mk
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:04:25.333882+00:00
-- url     : https://prove2.me/theorems/581f913e-3a04-586b-a220-0a0e3821d743
-- title:
--   R: gamma Chart symm mk
-- statement:
--   The R construction uses the gamma Chart symm mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjDehom.lean#L255-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjDehom.lean#L255-L270

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SegreIdealIsHomogeneous
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehom
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

theorem ReciprocityTheory.AnForm.R.gammaChart_symm_mk {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (p : (k : K) → ι k) (f : MvPolynomial (Σ k, ι k) ℂ) :
    (gammaChart hP p).symm (Ideal.Quotient.mk _ f) =
      eval₂ (constSec (toSpecC hP) (chartOpen hP p).1) (chartCoord hP p) f := by sorry
