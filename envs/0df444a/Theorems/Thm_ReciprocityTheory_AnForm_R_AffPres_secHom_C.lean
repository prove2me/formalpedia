-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_AffPres_secHom_C
-- name    : ReciprocityTheory.AnForm.R.AffPres.secHom_C
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:38:01.619674+00:00
-- url     : https://prove2.me/theorems/42cc7247-d2e6-51d9-925e-e886feaca729
-- title:
--   Aff Pres: sec Hom C
-- statement:
--   The Aff Pres construction uses the sec Hom C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/SecHomSurjective.lean#L32-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/SecHomSurjective.lean#L32-L45

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SecHomSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory MvPolynomial
noncomputable section
variable {W : Scheme.{0}} {sW : W ⟶ Spec (.of ℂ)}
open ReciprocityTheory.AnForm.R.AffPres
set_option backward.isDefEq.respectTransparency false

theorem ReciprocityTheory.AnForm.R.AffPres.secHom_C (P : AffPres sW) (c : ℂ) : P.secHom (C c) = constSec sW P.V c := by sorry
