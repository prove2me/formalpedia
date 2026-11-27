-- Prove2me | Theorems.Thm_PositivityTheory_FamInh_comap_connectedComponent
-- name    : PositivityTheory.FamInh.comap_connectedComponent
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:50:00.891598+00:00
-- url     : https://prove2.me/theorems/a000d091-d6cc-54aa-8fa2-c5f8fbb020a1
-- title:
--   Fam Inh: comap connected Component
-- statement:
--   The Fam Inh construction uses the comap connected Component property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PlaceConnectedComponents/ArtinKer.lean#L30-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PlaceConnectedComponents/ArtinKer.lean#L30-L85

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeCharRayClass
import Definitions.Def_Development_WeilBound_CoreStatements_PlaceConnectedComponents_ArtinKer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Topology GroundTheory.Global GroundTheory.Global.IdeleGroup
open PositivityTheory PositivityTheory.FamInh

theorem PositivityTheory.FamInh.comap_connectedComponent (E : Type) [Field E] [NumberField E] :
    (Subgroup.connectedComponentOfOne (GroundTheory.Global.IdeleClassGroup E)).comap (GroundTheory.Global.IdeleClassGroup.mk E) =
      ((Neutral.B1.diagUnits E).range ⊔ GlobalTheory.HeckeGal.infConn E).topologicalClosure := by sorry
