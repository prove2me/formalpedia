-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_ker_preimage___comp_of_isIso_852b3ee68910
-- name    : P2M_FunctorialResolution_EmbeddedResolution_ker_preimage___comp_of_isIso_852b3ee68910
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:02:34.673156+00:00
-- url     : https://prove2.me/theorems/5c6c3803-9bac-456b-b1e4-777ca723ba66
-- title:
--   P2 M Functorial Resolution Embedded Resolution ker preimage   comp of is Iso 852b3ee68910: P2 M Functorial Resolution Embedded Resolution ker preimage   comp of is Iso 852b3ee68910
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution ker preimage   comp of is Iso 852b3ee68910 construction uses the P2 M Functorial Resolution Embedded Resolution ker preimage   comp of is Iso 852b3ee68910 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/ClosedEmbedding/IsoBlowupPushforward.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/ClosedEmbedding/IsoBlowupPushforward.lean#L22-L26

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReduction_IsomorphismTransport
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_ClosedEmbedding_IsoBlowupPushforward
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem P2M_FunctorialResolution_EmbeddedResolution_ker_preimage___comp_of_isIso_852b3ee68910 {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (U : Y.Opens) :
    ((f ⁻¹ᵁ U).ι ≫ f).ker = U.ι.ker := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«ker_preimage_ι_comp_of_isIso» := P2M_FunctorialResolution_EmbeddedResolution_ker_preimage___comp_of_isIso_852b3ee68910
