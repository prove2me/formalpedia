-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_InterNumPointDeg_primeOf_pt_8320e87d5386
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_InterNumPointDeg_primeOf_pt_8320e87d5386
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:15:44.464694+00:00
-- url     : https://prove2.me/theorems/71e01481-d278-4421-9314-8c2e6cb22a8d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Inter Num Point Deg prime Of pt 8320e87d5386: P2 M Ground Theory Heights  Heights Kleiman Inter Num Point Deg prime Of pt 8320e87d5386
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Inter Num Point Deg prime Of pt 8320e87d5386 construction uses the P2 M Ground Theory Heights  Heights Kleiman Inter Num Point Deg prime Of pt 8320e87d5386 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumPointDeg.lean#L69-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumPointDeg.lean#L69-L81

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_InterNumPointDeg_primeOf_pt_8320e87d5386 (hh : ∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp) :
    primeOf (S := k) (pt.{u, w} pp) = pp := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«InterNumPointDeg».«primeOf_pt» := P2M_GroundTheory_Heights__Heights_Kleiman_InterNumPointDeg_primeOf_pt_8320e87d5386
