-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecKer_ker_eq_d460a27c2b3a
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_GenSecKer_ker_eq_d460a27c2b3a
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:42:29.068733+00:00
-- url     : https://prove2.me/theorems/81985514-0d9a-4590-a156-a68ef5f9170e
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Gen Sec Ker ker eq d460a27c2b3a: P2 M Ground Theory Heights  Heights Vertical Gen Sec Ker ker eq d460a27c2b3a
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Gen Sec Ker ker eq d460a27c2b3a construction uses the P2 M Ground Theory Heights  Heights Vertical Gen Sec Ker ker eq d460a27c2b3a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecKer.lean#L40-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecKer.lean#L40-L188

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDimStrictDrop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsGenSecKer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGenSecKer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial Cardinal
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.GenSecKer

theorem P2M_GroundTheory_Heights__Heights_Vertical_GenSecKer_ker_eq_d460a27c2b3a {k L : Type} [Field k] [CommRing L] (hL : IsField L) [Algebra k L] {n e : ℕ}
    [Algebra (GenParField k e n) L] [IsScalarTower k (GenParField k e n) L]
    (Q : Ideal (MvPolynomial (Fin n) k)) [Q.IsPrime]
    (hdim : ringKrullDim (MvPolynomial (Fin n) k ⧸ Q) = ((e + 1 : ℕ) : WithBot ℕ∞)) (x : Fin n → L)
    (hgen : ∀ z : L, ∃ p : MvPolynomial (Fin n) (GenParField k e n), aeval x p = z)
    (hR1 : ∀ i : Fin e, ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inl (i, j))) * x j = 0)
    (hR2 : ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inr j)) * x j = 1)
    (hQ : ∀ q ∈ Q, aeval x q = 0) :
    RingHom.ker (aeval x : MvPolynomial (Fin n) k →ₐ[k] L) = Q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«GenSecKer».«ker_eq» := P2M_GroundTheory_Heights__Heights_Vertical_GenSecKer_ker_eq_d460a27c2b3a
