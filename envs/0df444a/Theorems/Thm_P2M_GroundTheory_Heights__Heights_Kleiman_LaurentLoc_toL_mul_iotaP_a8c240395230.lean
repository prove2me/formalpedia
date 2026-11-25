-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_toL_mul_iotaP_a8c240395230
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_toL_mul_iotaP_a8c240395230
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:30:03.765377+00:00
-- url     : https://prove2.me/theorems/c826ac38-685e-4175-a943-d2f69200bb72
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Laurent Loc to L mul iota P a8c240395230: P2 M Ground Theory Heights  Heights Kleiman Laurent Loc to L mul iota P a8c240395230
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Laurent Loc to L mul iota P a8c240395230 construction uses the P2 M Ground Theory Heights  Heights Kleiman Laurent Loc to L mul iota P a8c240395230 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L109-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L109-L111

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
attribute [local instance] algP

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_toL_mul_iotaP_a8c240395230 (I : Finset (Fin (N + 1))) (p : Poly S N) (s : monos (S := S) I) :
    toL S N p = toL S N s * iotaP I (LocalizedModule.mk p s) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LaurentLoc».«toL_mul_iotaP» := P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_toL_mul_iotaP_a8c240395230
