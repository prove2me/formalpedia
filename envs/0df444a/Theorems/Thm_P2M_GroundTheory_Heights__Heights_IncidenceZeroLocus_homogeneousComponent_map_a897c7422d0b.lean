-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IncidenceZeroLocus_homogeneousComponent_map_a897c7422d0b
-- name    : P2M_GroundTheory_Heights__Heights_IncidenceZeroLocus_homogeneousComponent_map_a897c7422d0b
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:20:06.289608+00:00
-- url     : https://prove2.me/theorems/6fe44423-29c5-46fc-bda7-882aadbebb5b
-- title:
--   P2 M Ground Theory Heights  Heights Incidence Zero Locus homogeneous Component map a897c7422d0b: P2 M Ground Theory Heights  Heights Incidence Zero Locus homogeneous Component map a897c7422d0b
-- statement:
--   The P2 M Ground Theory Heights  Heights Incidence Zero Locus homogeneous Component map a897c7422d0b construction uses the P2 M Ground Theory Heights  Heights Incidence Zero Locus homogeneous Component map a897c7422d0b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PIncidenceZeroLocus.lean#L35-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PIncidenceZeroLocus.lean#L35-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PIncidenceZeroLocus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.IncidenceZeroLocus

theorem P2M_GroundTheory_Heights__Heights_IncidenceZeroLocus_homogeneousComponent_map_a897c7422d0b {R S σ : Type*} [CommSemiring R] [CommSemiring S] (g : R →+* S)
    (N : ℕ) (p : MvPolynomial σ R) :
    homogeneousComponent N (map g p) = map g (homogeneousComponent N p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IncidenceZeroLocus».«homogeneousComponent_map» := P2M_GroundTheory_Heights__Heights_IncidenceZeroLocus_homogeneousComponent_map_a897c7422d0b
