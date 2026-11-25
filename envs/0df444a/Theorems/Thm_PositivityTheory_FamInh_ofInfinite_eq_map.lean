-- Prove2me | Theorems.Thm_PositivityTheory_FamInh_ofInfinite_eq_map
-- name    : PositivityTheory.FamInh.ofInfinite_eq_map
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:52:00.505447+00:00
-- url     : https://prove2.me/theorems/424e9456-5817-5d92-baca-7c6f98d0d865
-- title:
--   Fam Inh: of Infinite eq map
-- statement:
--   The Fam Inh construction uses the of Infinite eq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PlaceConnectedComponents/ArtinKer.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PlaceConnectedComponents/ArtinKer.lean#L25-L28

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

theorem PositivityTheory.FamInh.ofInfinite_eq_map (E : Type) [Field E] [NumberField E] (y : (InfiniteAdeleRing E)ˣ) :
    (ofInfinite y : IdeleGroup E) =
      Units.map (MonoidHom.inl (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)) y := by sorry
