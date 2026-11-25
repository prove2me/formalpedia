-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_R_effCartier_comap_of_isOpenImmersion__bb69f67b52e9
-- name    : P2M_ReciprocityTheory_AnForm_R_effCartier_comap_of_isOpenImmersion__bb69f67b52e9
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:30:23.976475+00:00
-- url     : https://prove2.me/theorems/6f0cf7fa-7ccf-5bbf-a8a6-ba3375a746ce
-- title:
--   P2 M Reciprocity Theory An Form R eff Cartier comap of is Open Immersion  bb69f67b52e9: P2 M Reciprocity Theory An Form R eff Cartier comap of is Open Immersion  bb69f67b52e9
-- statement:
--   The P2 M Reciprocity Theory An Form R eff Cartier comap of is Open Immersion  bb69f67b52e9 construction uses the P2 M Reciprocity Theory An Form R eff Cartier comap of is Open Immersion  bb69f67b52e9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WChartsB.lean#L66-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WChartsB.lean#L66-L89

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory
noncomputable section

theorem P2M_ReciprocityTheory_AnForm_R_effCartier_comap_of_isOpenImmersion__bb69f67b52e9 {X Y : Scheme.{0}} (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] (hI : FinalTheorems.EffCartier I) : FinalTheorems.EffCartier (I.comap f) := by sorry

alias «ReciprocityTheory».«AnForm».«R».«effCartier_comap_of_isOpenImmersion'» := P2M_ReciprocityTheory_AnForm_R_effCartier_comap_of_isOpenImmersion__bb69f67b52e9
