-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_iota_apply_bc280d50aeac
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_iota_apply_bc280d50aeac
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:22.093797+00:00
-- url     : https://prove2.me/theorems/039808ac-8f7d-44cb-a95e-9536c8c5ce00
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Laurent Loc iota apply bc280d50aeac: P2 M Ground Theory Heights  Heights Kleiman Laurent Loc iota apply bc280d50aeac
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Laurent Loc iota apply bc280d50aeac construction uses the P2 M Ground Theory Heights  Heights Kleiman Laurent Loc iota apply bc280d50aeac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L133-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L133-L133

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
variable {S : Type u} [CommRing S] {N : ℕ}
attribute [local instance] algP

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_iota_apply_bc280d50aeac (I : StdCell N) (z : LocMod S N (Poly S N) I.1) : iota I z = (iotaP I.1 z).coeff := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LaurentLoc».«iota_apply» := P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_iota_apply_bc280d50aeac
