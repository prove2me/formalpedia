-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleRingFiniteType_ampleChart_le_64c0456cd574
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_AmpleRingFiniteType_ampleChart_le_64c0456cd574
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:00:40.052094+00:00
-- url     : https://prove2.me/theorems/9f532bcd-5f4a-5d11-9019-e7a2a87ae07e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ample Ring Finite Type ample Chart le 64c0456cd574: P2 M Ground Theory Heights  Heights Kleiman Ample Ring Finite Type ample Chart le 64c0456cd574
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ample Ring Finite Type ample Chart le 64c0456cd574 construction uses the P2 M Ground Theory Heights  Heights Kleiman Ample Ring Finite Type ample Chart le 64c0456cd574 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleRingFiniteType.lean#L84-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleRingFiniteType.lean#L84-L122

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AmpleRingFiniteTypeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleRingFiniteType
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
open GroundTheory.Heights₂.Heights.Kleiman.AmpleRingFiniteType
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_AmpleRingFiniteType_ampleChart_le_64c0456cd574 (H : LineBundle S x) (D : AmpleData S x H) (j : Fin (D.r + 1))
    (h0 : D.h j ≠ 0) (J : Chart x) {a : Ω} (ha : a ∈ ampleChart H.toSubSystem D.m (D.h j) J) :
    a ∈ Algebra.adjoin S (Set.range (fun l => D.h l / D.h j) ∪ (chartGens J : Set Ω)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«AmpleRingFiniteType».«ampleChart_le» := P2M_GroundTheory_Heights__Heights_Kleiman_AmpleRingFiniteType_ampleChart_le_64c0456cd574
