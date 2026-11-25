-- Prove2me | Theorems.Thm_PositivityTheory_FamInh_isOpen_connInf
-- name    : PositivityTheory.FamInh.isOpen_connInf
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:56:29.610043+00:00
-- url     : https://prove2.me/theorems/d7c53138-1875-538c-9802-0ba307da0e44
-- title:
--   Fam Inh: is Open conn Inf
-- statement:
--   The Fam Inh construction uses the is Open conn Inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PlaceConnectedComponents/ArtinKer.lean#L11-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PlaceConnectedComponents/ArtinKer.lean#L11-L23

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

theorem PositivityTheory.FamInh.isOpen_connInf (E : Type) [Field E] [NumberField E] :
    IsOpen ((Subgroup.connectedComponentOfOne (InfiniteAdeleRing E)ˣ : Subgroup (InfiniteAdeleRing E)ˣ) :
      Set (InfiniteAdeleRing E)ˣ) := by sorry
