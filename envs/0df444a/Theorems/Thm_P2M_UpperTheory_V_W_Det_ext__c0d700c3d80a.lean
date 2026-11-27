-- Prove2me | Theorems.Thm_P2M_UpperTheory_V_W_Det_ext__c0d700c3d80a
-- name    : P2M_UpperTheory_V_W_Det_ext__c0d700c3d80a
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:23:27.098707+00:00
-- url     : https://prove2.me/theorems/c0671fce-ba10-4699-89fb-518153b8cea6
-- title:
--   P2 M Upper Theory V W Det ext  c0d700c3d80a: P2 M Upper Theory V W Det ext  c0d700c3d80a
-- statement:
--   The P2 M Upper Theory V W Det ext  c0d700c3d80a construction uses the P2 M Upper Theory V W Det ext  c0d700c3d80a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebraHeight/OfDetToDet.lean#L135-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebraHeight/OfDetToDet.lean#L135-L136

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
open UpperTheory.V.W.Det
variable {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E)

theorem P2M_UpperTheory_V_W_Det_ext__c0d700c3d80a {D D' : Det n A E} (h : ∀ (S : Type) [CommRing S] [Algebra A S] (x), D.D S x = D'.D S x) : D = D' := by sorry

alias «UpperTheory».«V».«W».«Det».«ext'» := P2M_UpperTheory_V_W_Det_ext__c0d700c3d80a
