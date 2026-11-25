-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locRes_self_fe16e7a28657
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_locRes_self_fe16e7a28657
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:28:32.317144+00:00
-- url     : https://prove2.me/theorems/66b74fce-5869-4bae-804d-1cbd32ebd38a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman loc Res self fe16e7a28657: P2 M Ground Theory Heights  Heights Kleiman loc Res self fe16e7a28657
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman loc Res self fe16e7a28657 construction uses the P2 M Ground Theory Heights  Heights Kleiman loc Res self fe16e7a28657 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwistSections.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwistSections.lean#L28-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTwistSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotGraded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwistSections
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
universe u w
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type*} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_locRes_self_fe16e7a28657 {I : Finset (Fin (N + 1))} (h : I ⊆ I) (x : LocMod S N M I) : locRes h x = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«locRes_self» := P2M_GroundTheory_Heights__Heights_Kleiman_locRes_self_fe16e7a28657
