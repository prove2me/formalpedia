-- Prove2me | Theorems.Thm_UpperTheory_V_W_GDet_ofDet_toDet
-- name    : UpperTheory.V.W.GDet.ofDet_toDet
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:23:42.350331+00:00
-- url     : https://prove2.me/theorems/2aded37e-fba4-46ae-a8b8-7196ccdb14e8
-- title:
--   GDet: of Det to Det
-- statement:
--   The GDet construction uses the of Det to Det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebraHeight/OfDetToDet.lean#L209-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebraHeight/OfDetToDet.lean#L209-L210

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_WeilGroupCharacters_RepAlg
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_UnopSMul
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_CommutativeAlgebraHeight_OfDetToDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing
open UpperTheory UpperTheory.V UpperTheory.V.W
open UpperTheory.V.W.GDet
variable {n : ℕ} {A G : Type} [CommRing A] [Group G]

theorem UpperTheory.V.W.GDet.ofDet_toDet (D : GDet n A G) : ofDet D.toDet = D := by sorry
