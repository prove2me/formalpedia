-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locMap_retract_393d1aa75454
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_locMap_retract_393d1aa75454
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:24.233063+00:00
-- url     : https://prove2.me/theorems/d1185e8a-d351-497c-b525-01abcdee2094
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman loc Map retract 393d1aa75454: P2 M Ground Theory Heights  Heights Kleiman loc Map retract 393d1aa75454
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman loc Map retract 393d1aa75454 construction uses the P2 M Ground Theory Heights  Heights Kleiman loc Map retract 393d1aa75454 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCohomRetract.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCohomRetract.lean#L21-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsPres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCohomRetract
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
universe u v w
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]
variable {M' : Type w} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']

theorem P2M_GroundTheory_Heights__Heights_Kleiman_locMap_retract_393d1aa75454 (f : M →ₗ[Poly S N] M') (g : M' →ₗ[Poly S N] M)
    (hgf : Function.LeftInverse g f) (I : Finset (Fin (N + 1))) :
    Function.LeftInverse (locMap g I) (locMap f I) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«locMap_retract» := P2M_GroundTheory_Heights__Heights_Kleiman_locMap_retract_393d1aa75454
