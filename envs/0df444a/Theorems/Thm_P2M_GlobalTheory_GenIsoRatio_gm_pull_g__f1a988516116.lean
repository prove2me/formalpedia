-- Prove2me | Theorems.Thm_P2M_GlobalTheory_GenIsoRatio_gm_pull_g__f1a988516116
-- name    : P2M_GlobalTheory_GenIsoRatio_gm_pull_g__f1a988516116
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:06:48.829145+00:00
-- url     : https://prove2.me/theorems/0e4f9c7a-f84d-4dc8-8e3d-0aef0e030f95
-- title:
--   P2 M Global Theory Gen Iso Ratio gm pull g  f1a988516116: P2 M Global Theory Gen Iso Ratio gm pull g  f1a988516116
-- statement:
--   The P2 M Global Theory Gen Iso Ratio gm pull g  f1a988516116 construction uses the P2 M Global Theory Gen Iso Ratio gm pull g  f1a988516116 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGlobalUnitRatioGenericLineBundleIsos.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGlobalUnitRatioGenericLineBundleIsos.lean#L16-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_RigidifiedPartialLineBundleIsoCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlobalUnitRatioGenericLineBundleIsos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.GenIsoRatio

theorem P2M_GlobalTheory_GenIsoRatio_gm_pull_g__f1a988516116 {X Y : Scheme.{0}} (β : Y ⟶ X) (L : LB X) (y : Y) (i i' : L.ι) (hi : β y ∈ L.U i)
    (hi' : β y ∈ L.U i') :
    gm (𝟙 Y) y ((L.pull β).U (fun _ => i) ⊓ (L.pull β).U (fun _ => i'))
      ((L.pull β).g (fun _ => i) (fun _ => i')) = gm β y (L.U i ⊓ L.U i') (L.g i i') := by sorry

alias «GlobalTheory».«GenIsoRatio».«gm_pull_g'» := P2M_GlobalTheory_GenIsoRatio_gm_pull_g__f1a988516116
