-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormDimLe_exists_prime_liesOver_ad270c783d28
-- name    : P2M_GroundTheory_Heights__Heights_ChowFormDimLe_exists_prime_liesOver_ad270c783d28
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:38:23.77673+00:00
-- url     : https://prove2.me/theorems/83e966da-7716-48b8-b3e7-59365254ddab
-- title:
--   P2 M Ground Theory Heights  Heights Chow Form Dim Le exists prime lies Over ad270c783d28: P2 M Ground Theory Heights  Heights Chow Form Dim Le exists prime lies Over ad270c783d28
-- statement:
--   The P2 M Ground Theory Heights  Heights Chow Form Dim Le exists prime lies Over ad270c783d28 construction uses the P2 M Ground Theory Heights  Heights Chow Form Dim Le exists prime lies Over ad270c783d28 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowFormDimLe.lean#L21-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowFormDimLe.lean#L21-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChowFormDim
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormDimLe
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
open GroundTheory.Heights₂.Heights.ChowFormDimLe

theorem P2M_GroundTheory_Heights__Heights_ChowFormDimLe_exists_prime_liesOver_ad270c783d28 {F : Type} [Field F] (K : Type) [Field K] [Algebra F K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) F)) [I.IsPrime] (hI : ∀ g ∈ I, coeff 0 g = 0) :
    ∃ P : Ideal (MvPolynomial (Fin n) K), P.IsPrime ∧
      P ≤ RingHom.ker (eval (0 : Fin n → K)) ∧
      P.comap (MvPolynomial.map (algebraMap F K)) = I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowFormDimLe».«exists_prime_liesOver» := P2M_GroundTheory_Heights__Heights_ChowFormDimLe_exists_prime_liesOver_ad270c783d28
