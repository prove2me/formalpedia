-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locMap_comp_locResS_e33ebeba7576
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_locMap_comp_locResS_e33ebeba7576
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:33:51.668799+00:00
-- url     : https://prove2.me/theorems/26ba3e62-9320-4bb7-93ce-5cbbda2c7185
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman loc Map comp loc Res S e33ebeba7576: P2 M Ground Theory Heights  Heights Kleiman loc Map comp loc Res S e33ebeba7576
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman loc Map comp loc Res S e33ebeba7576 construction uses the P2 M Ground Theory Heights  Heights Kleiman loc Map comp loc Res S e33ebeba7576 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechExact.lean#L295-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechExact.lean#L295-L300

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsDegLocExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechExact
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
universe u v
universe w
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]
variable {M' : Type w} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']

theorem P2M_GroundTheory_Heights__Heights_Kleiman_locMap_comp_locResS_e33ebeba7576 (f : M →ₗ[Poly S N] M') (I J : StdCell N) (h : I.1 ⊆ J.1)
    (x : LocMod S N M I.1) : locMap f J.1 (locResS I J h x) = locResS I J h (locMap f I.1 x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«locMap_comp_locResS» := P2M_GroundTheory_Heights__Heights_Kleiman_locMap_comp_locResS_e33ebeba7576
