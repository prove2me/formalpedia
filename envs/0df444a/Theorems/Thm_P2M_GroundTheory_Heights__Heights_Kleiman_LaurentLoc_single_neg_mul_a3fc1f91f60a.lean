-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_single_neg_mul_a3fc1f91f60a
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_single_neg_mul_a3fc1f91f60a
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:27:12.604969+00:00
-- url     : https://prove2.me/theorems/3368011a-2ff2-4f19-82f6-a32f747ff2a5
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Laurent Loc single neg mul a3fc1f91f60a: P2 M Ground Theory Heights  Heights Kleiman Laurent Loc single neg mul a3fc1f91f60a
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Laurent Loc single neg mul a3fc1f91f60a construction uses the P2 M Ground Theory Heights  Heights Kleiman Laurent Loc single neg mul a3fc1f91f60a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L44-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L44-L47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
variable (S : Type u) [CommRing S] (N : ℕ)
variable {S N}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_single_neg_mul_a3fc1f91f60a (b : Fin (N + 1) → ℤ) (x : LRing S N) :
    AddMonoidAlgebra.single (-b) (1 : S) * (AddMonoidAlgebra.single b 1 * x) = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LaurentLoc».«single_neg_mul» := P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_single_neg_mul_a3fc1f91f60a
