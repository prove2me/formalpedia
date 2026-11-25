-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_AffPres_eval_coord_eq_val
-- name    : ReciprocityTheory.AnForm.R.AffPres.eval_coord_eq_val
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:38:50.094243+00:00
-- url     : https://prove2.me/theorems/f7e6e5c0-1b08-585a-9319-2321ddc962ce
-- title:
--   Aff Pres: eval coord eq val
-- statement:
--   The Aff Pres construction uses the eval coord eq val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/MemBasicOpenSecHomIff.lean#L60-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/MemBasicOpenSecHomIff.lean#L60-L94

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemBasicOpenSecHomIff
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
variable {W : Scheme.{0}} {s : W ⟶ Spec (.of ℂ)}
open ReciprocityTheory.AnForm.R.AffPres
variable (P : AffPres s)

theorem ReciprocityTheory.AnForm.R.AffPres.eval_coord_eq_val [LocallyOfFiniteType s] (x : W) (hx : x ∈ P.V)
    (hc : IsClosed ({x} : Set W)) (f : MvPolynomial (Fin P.n) ℂ) :
    eval (P.coord x hx) f = val s (P.secHom f) x hx := by sorry
