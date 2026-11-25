-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_AffPres_mem_basicOpen_secHom_iff
-- name    : ReciprocityTheory.AnForm.R.AffPres.mem_basicOpen_secHom_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:38:57.195677+00:00
-- url     : https://prove2.me/theorems/6ef7c9cb-908c-59dc-9cee-652b4c3e2320
-- title:
--   Aff Pres: mem basic Open sec Hom iff
-- statement:
--   The Aff Pres construction uses the mem basic Open sec Hom iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/MemBasicOpenSecHomIff.lean#L16-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/MemBasicOpenSecHomIff.lean#L16-L36

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

theorem ReciprocityTheory.AnForm.R.AffPres.mem_basicOpen_secHom_iff (x : W) (hx : x ∈ P.V) (f : MvPolynomial (Fin P.n) ℂ) :
    x ∈ W.basicOpen (P.secHom f) ↔ f ∉ P.ptOf x hx := by sorry
