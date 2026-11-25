-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SecRankSpecialize_mem_maximalIdeal_smul_of_secMap_eq_zero_17f6f7b6cd36
-- name    : P2M_GroundTheory_Heights__Heights_SecRankSpecialize_mem_maximalIdeal_smul_of_secMap_eq_zero_17f6f7b6cd36
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:08:55.163545+00:00
-- url     : https://prove2.me/theorems/7583d968-1d0c-5373-94cd-2e39d819d8f6
-- title:
--   P2 M Ground Theory Heights  Heights Sec Rank Specialize mem maximal Ideal smul of sec Map eq zero 17f6f7b6cd36: P2 M Ground Theory Heights  Heights Sec Rank Specialize mem maximal Ideal smul of sec Ma
-- statement:
--   The P2 M Ground Theory Heights  Heights Sec Rank Specialize mem maximal Ideal smul of sec Map eq zero 17f6f7b6cd36 construction uses the P2 M Ground Theory Heights  Heights Sec Rank Specialize mem maximal Ideal smul of sec Map eq zero 17f6f7b6cd36 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSecRankSpecialize.lean#L27-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSecRankSpecialize.lean#L27-L47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSecRankSpecialize
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecAlgFieldChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSecRankSpecialize
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
open GroundTheory.Heights₂.Heights.SecRankSpecialize
open Vertical

theorem P2M_GroundTheory_Heights__Heights_SecRankSpecialize_mem_maximalIdeal_smul_of_secMap_eq_zero_17f6f7b6cd36 {R : Type*} [CommRing R] [IsLocalRing R]
    (κ : Type*) [Field κ] [Algebra R κ] (hsurj : Function.Surjective (algebraMap R κ)) {n e : ℕ}
    (Q : Ideal (MvPolynomial (Fin n) R)) (y : Par e n → R) (x : SecAlg Q y)
    (hx : secMap κ Q y x = 0) :
    x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R (SecAlg Q y)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SecRankSpecialize».«mem_maximalIdeal_smul_of_secMap_eq_zero» := P2M_GroundTheory_Heights__Heights_SecRankSpecialize_mem_maximalIdeal_smul_of_secMap_eq_zero_17f6f7b6cd36
