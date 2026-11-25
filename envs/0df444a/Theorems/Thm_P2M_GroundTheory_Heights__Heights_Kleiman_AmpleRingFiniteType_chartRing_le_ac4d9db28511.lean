-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleRingFiniteType_chartRing_le_ac4d9db28511
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_AmpleRingFiniteType_chartRing_le_ac4d9db28511
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:58:55.517734+00:00
-- url     : https://prove2.me/theorems/98c06613-c50d-44fe-be35-dbf9b24bc0e0
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ample Ring Finite Type chart Ring le ac4d9db28511: P2 M Ground Theory Heights  Heights Kleiman Ample Ring Finite Type chart Ring le ac4d9db28511
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ample Ring Finite Type chart Ring le ac4d9db28511 construction uses the P2 M Ground Theory Heights  Heights Kleiman Ample Ring Finite Type chart Ring le ac4d9db28511 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleRingFiniteType.lean#L47-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleRingFiniteType.lean#L47-L82

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_AmpleRingFiniteType_chartRing_le_ac4d9db28511 (J : Chart x) :
    chartRing S x J ≤ Algebra.adjoin S (chartGens J : Set Ω) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«AmpleRingFiniteType».«chartRing_le» := P2M_GroundTheory_Heights__Heights_Kleiman_AmpleRingFiniteType_chartRing_le_ac4d9db28511
