-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_StalkLocB_phiE_mk
-- name    : ReciprocityTheory.AnForm.R.StalkLocB.phiE_mk
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:02:33.326155+00:00
-- url     : https://prove2.me/theorems/2760428a-e5f1-4045-9e62-1b55ea5b96c6
-- title:
--   Stalk Loc B: phi E mk
-- statement:
--   The Stalk Loc B construction uses the phi E mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/StalkLocB.lean#L48-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/StalkLocB.lean#L48-L49

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory MvPolynomial
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
noncomputable section
open ReciprocityTheory.AnForm.R.StalkLocB
variable {W : Scheme.{0}} (V : W.Opens) {n : ℕ} (K : Ideal (MvPolynomial (Fin n) ℂ))
  (iso : V.toScheme ≅ Spec (.of (MvPolynomial (Fin n) ℂ ⧸ K)))

theorem ReciprocityTheory.AnForm.R.StalkLocB.phiE_mk (f : MvPolynomial (Fin n) ℂ) :
    phiE V K iso (Ideal.Quotient.mk K f) = secH V K iso f := by sorry
