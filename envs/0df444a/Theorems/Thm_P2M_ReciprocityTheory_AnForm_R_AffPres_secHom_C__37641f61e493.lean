-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_R_AffPres_secHom_C__37641f61e493
-- name    : P2M_ReciprocityTheory_AnForm_R_AffPres_secHom_C__37641f61e493
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:40:46.365958+00:00
-- url     : https://prove2.me/theorems/2e32b1b1-832d-40f6-b537-fd907fddc520
-- title:
--   P2 M Reciprocity Theory An Form R Aff Pres sec Hom C  37641f61e493: P2 M Reciprocity Theory An Form R Aff Pres sec Hom C  37641f61e493
-- statement:
--   The P2 M Reciprocity Theory An Form R Aff Pres sec Hom C  37641f61e493 construction uses the P2 M Reciprocity Theory An Form R Aff Pres sec Hom C  37641f61e493 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/MemBasicOpenSecHomIff.lean#L38-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/MemBasicOpenSecHomIff.lean#L38-L58

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

theorem P2M_ReciprocityTheory_AnForm_R_AffPres_secHom_C__37641f61e493 (c : ℂ) : P.secHom (C c) = constSec s P.V c := by sorry

alias «ReciprocityTheory».«AnForm».«R».«AffPres».«secHom_C'» := P2M_ReciprocityTheory_AnForm_R_AffPres_secHom_C__37641f61e493
