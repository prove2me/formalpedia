-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_one_le_of_isProjPrime_d1887d63bb03
-- name    : P2M_GroundTheory_Heights__Heights_one_le_of_isProjPrime_d1887d63bb03
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:04:37.236383+00:00
-- url     : https://prove2.me/theorems/bb58a05d-7917-43f1-a889-0cf6bfca7e63
-- title:
--   P2 M Ground Theory Heights  Heights one le of is Proj Prime d1887d63bb03: P2 M Ground Theory Heights  Heights one le of is Proj Prime d1887d63bb03
-- statement:
--   The P2 M Ground Theory Heights  Heights one le of is Proj Prime d1887d63bb03 construction uses the P2 M Ground Theory Heights  Heights one le of is Proj Prime d1887d63bb03 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChowFormExists.lean#L21-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChowFormExists.lean#L21-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormExists
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

theorem P2M_GroundTheory_Heights__Heights_one_le_of_isProjPrime_d1887d63bb03 {F : Type*} [Field F] {n k : ℕ}
    {P : Ideal (MvPolynomial (Fin n) F)} (hP : IsProjPrime P)
    (hk : ringKrullDim (MvPolynomial (Fin n) F ⧸ P) = ((k : ℕ) : WithBot ℕ∞)) : 1 ≤ k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«one_le_of_isProjPrime» := P2M_GroundTheory_Heights__Heights_one_le_of_isProjPrime_d1887d63bb03
