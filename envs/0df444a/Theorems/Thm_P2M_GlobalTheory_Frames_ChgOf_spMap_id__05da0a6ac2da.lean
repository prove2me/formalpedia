-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Frames_ChgOf_spMap_id__05da0a6ac2da
-- name    : P2M_GlobalTheory_Frames_ChgOf_spMap_id__05da0a6ac2da
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:05:51.17183+00:00
-- url     : https://prove2.me/theorems/2b8feb75-4a7d-4b33-a030-9a44bf69d5cc
-- title:
--   P2 M Global Theory Frames Chg Of sp Map id  05da0a6ac2da: P2 M Global Theory Frames Chg Of sp Map id  05da0a6ac2da
-- statement:
--   The P2 M Global Theory Frames Chg Of sp Map id  05da0a6ac2da construction uses the P2 M Global Theory Frames Chg Of sp Map id  05da0a6ac2da property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FrameChangeExistsUniqueOfSamePoint.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FrameChangeExistsUniqueOfSamePoint.lean#L44-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsTangentModuleUniversalGroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FrameChangeExistsUniqueOfSamePoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open GlobalTheory GlobalTheory.Frames GlobalTheory.Frames.ChgOf
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem P2M_GlobalTheory_Frames_ChgOf_spMap_id__05da0a6ac2da (S : Type) [CommRing S] : spMap (RingHom.id S) = 𝟙 (Sp S) := by sorry

alias «GlobalTheory».«Frames».«ChgOf».«spMap_id'» := P2M_GlobalTheory_Frames_ChgOf_spMap_id__05da0a6ac2da
