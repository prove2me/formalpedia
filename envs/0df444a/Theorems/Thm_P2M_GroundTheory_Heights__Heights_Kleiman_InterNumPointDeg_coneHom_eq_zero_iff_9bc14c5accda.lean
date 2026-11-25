-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_InterNumPointDeg_coneHom_eq_zero_iff_9bc14c5accda
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_InterNumPointDeg_coneHom_eq_zero_iff_9bc14c5accda
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:10:25.004983+00:00
-- url     : https://prove2.me/theorems/31b098cb-d002-46a4-98c0-5fb635dfa2ce
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Inter Num Point Deg cone Hom eq zero iff 9bc14c5accda: P2 M Ground Theory Heights  Heights Kleiman Inter Num Point Deg cone Hom eq zero iff 9bc14c5accda
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Inter Num Point Deg cone Hom eq zero iff 9bc14c5accda construction uses the P2 M Ground Theory Heights  Heights Kleiman Inter Num Point Deg cone Hom eq zero iff 9bc14c5accda property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumPointDeg.lean#L43-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumPointDeg.lean#L43-L49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumPointDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_InterNumRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PInterNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPositive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PInterNumPointDeg
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
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.InterNumPointDeg
variable {k : Type u} [Field k] {N : ℕ}
variable [Small.{w} k] (pp : Ideal (Poly k N)) [pp.IsPrime]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_InterNumPointDeg_coneHom_eq_zero_iff_9bc14c5accda (f : OneRing k N) :
    coneHom.{u, w} pp f = 0 ↔ oneBlock (S := k) (N := N) f ∈ pp := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«InterNumPointDeg».«coneHom_eq_zero_iff» := P2M_GroundTheory_Heights__Heights_Kleiman_InterNumPointDeg_coneHom_eq_zero_iff_9bc14c5accda
