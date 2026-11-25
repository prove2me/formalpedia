-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_finite_quot_e423b00c1db3
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_finite_quot_e423b00c1db3
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:05.88381+00:00
-- url     : https://prove2.me/theorems/e45d5264-6481-4305-8261-8a889e5934b7
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman finite quot e423b00c1db3: P2 M Ground Theory Heights  Heights Kleiman finite quot e423b00c1db3
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman finite quot e423b00c1db3 construction uses the P2 M Ground Theory Heights  Heights Kleiman finite quot e423b00c1db3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/QuotGraded.lean#L167-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/QuotGraded.lean#L167-L169

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotGraded
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
open MvPolynomial DirectSum
noncomputable section
universe u
variable {S : Type u} [CommRing S] {N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_finite_quot_e423b00c1db3 (p : Ideal (Poly S N)) : Module.Finite (Poly S N) (Poly S N ⧸ p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«finite_quot» := P2M_GroundTheory_Heights__Heights_Kleiman_finite_quot_e423b00c1db3
