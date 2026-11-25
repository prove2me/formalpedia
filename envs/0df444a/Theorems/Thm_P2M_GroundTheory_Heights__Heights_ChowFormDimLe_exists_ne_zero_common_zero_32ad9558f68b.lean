-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormDimLe_exists_ne_zero_common_zero_32ad9558f68b
-- name    : P2M_GroundTheory_Heights__Heights_ChowFormDimLe_exists_ne_zero_common_zero_32ad9558f68b
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:38:19.830024+00:00
-- url     : https://prove2.me/theorems/825f5add-cbe6-4962-bb5e-a993f22b3faa
-- title:
--   P2 M Ground Theory Heights  Heights Chow Form Dim Le exists ne zero common zero 32ad9558f68b: P2 M Ground Theory Heights  Heights Chow Form Dim Le exists ne zero common zero 32ad9558f68b
-- statement:
--   The P2 M Ground Theory Heights  Heights Chow Form Dim Le exists ne zero common zero 32ad9558f68b construction uses the P2 M Ground Theory Heights  Heights Chow Form Dim Le exists ne zero common zero 32ad9558f68b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowFormDimLe.lean#L51-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowFormDimLe.lean#L51-L121

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

theorem P2M_GroundTheory_Heights__Heights_ChowFormDimLe_exists_ne_zero_common_zero_32ad9558f68b {K : Type} [Field K] [IsAlgClosed K] {n k : ℕ}
    (P : Ideal (MvPolynomial (Fin n) K)) [P.IsPrime] (hPQ : P ≤ RingHom.ker (eval (0 : Fin n → K)))
    (hdim : (k : WithBot ℕ∞) < ringKrullDim (MvPolynomial (Fin n) K ⧸ P))
    (u : Fin k × Fin n → K) :
    ∃ x : Fin n → K, x ≠ 0 ∧ (∀ g ∈ P, eval x g = 0) ∧ ∀ i, ∑ j, u (i, j) * x j = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowFormDimLe».«exists_ne_zero_common_zero» := P2M_GroundTheory_Heights__Heights_ChowFormDimLe_exists_ne_zero_common_zero_32ad9558f68b
