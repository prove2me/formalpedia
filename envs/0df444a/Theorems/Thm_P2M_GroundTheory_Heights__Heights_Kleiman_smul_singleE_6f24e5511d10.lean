-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_smul_singleE_6f24e5511d10
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_smul_singleE_6f24e5511d10
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:51:16.618587+00:00
-- url     : https://prove2.me/theorems/d6c2e24c-f02c-4403-91fc-783371587b6b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman smul single E 6f24e5511d10: P2 M Ground Theory Heights  Heights Kleiman smul single E 6f24e5511d10
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman smul single E 6f24e5511d10 construction uses the P2 M Ground Theory Heights  Heights Kleiman smul single E 6f24e5511d10 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanishCone.lean#L106-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanishCone.lean#L106-L112

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanishCone
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
variable (S : Type u) [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
variable {S x E}
variable (S x E)
variable {S x E}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_smul_singleE_6f24e5511d10 {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) (c : ℤ) (v : E) :
    f • singleE S x E c v = singleE S x E (c + e) (aeval x f • v) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«smul_singleE» := P2M_GroundTheory_Heights__Heights_Kleiman_smul_singleE_6f24e5511d10
