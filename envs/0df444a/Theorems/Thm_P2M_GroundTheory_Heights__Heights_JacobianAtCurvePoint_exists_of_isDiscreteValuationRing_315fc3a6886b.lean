-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_JacobianAtCurvePoint_exists_of_isDiscreteValuationRing_315fc3a6886b
-- name    : P2M_GroundTheory_Heights__Heights_JacobianAtCurvePoint_exists_of_isDiscreteValuationRing_315fc3a6886b
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:26:05.23965+00:00
-- url     : https://prove2.me/theorems/95c524a2-15d0-41be-8ea2-da091c813c6c
-- title:
--   P2 M Ground Theory Heights  Heights Jacobian At Curve Point exists of is Discrete Valuation Ring 315fc3a6886b: P2 M Ground Theory Heights  Heights Jacobian At Curve Point exists of is Discrete Valuati
-- statement:
--   The P2 M Ground Theory Heights  Heights Jacobian At Curve Point exists of is Discrete Valuation Ring 315fc3a6886b construction uses the P2 M Ground Theory Heights  Heights Jacobian At Curve Point exists of is Discrete Valuation Ring 315fc3a6886b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/JacobianAtCurvePoint.lean#L41-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/JacobianAtCurvePoint.lean#L41-L270

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GradientAtPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelPlace
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_SmoothOfRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_JacobianAtCurvePoint
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
open MvPolynomial IsLocalRing GradientAtPoint
noncomputable section
open GroundTheory.Heights₂.Heights.JacobianAtCurvePoint
variable {σ : Type}
variable [Fintype σ]

theorem P2M_GroundTheory_Heights__Heights_JacobianAtCurvePoint_exists_of_isDiscreteValuationRing_315fc3a6886b (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ)
    (hw : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I) (S : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra (ptLoc w) S] [Algebra (MvPolynomial σ ℂ) S] [IsScalarTower (MvPolynomial σ ℂ) (ptLoc w) S]
    (hsurj : Function.Surjective (algebraMap (ptLoc w) S))
    (hker : RingHom.ker (algebraMap (ptLoc w) S) = ptIdeal I w) :
    ∃ (k : ℕ) (f : Fin k → MvPolynomial σ ℂ) (D : MvPolynomial σ ℂ),
      k + 1 = Fintype.card σ ∧ (∀ j, f j ∈ I) ∧
        LinearIndependent ℂ (fun j (i : σ) => eval w (pderiv i (f j))) ∧
        eval w D ≠ 0 ∧ ∀ p ∈ I, D * p ∈ Ideal.span (Set.range f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«JacobianAtCurvePoint».«exists_of_isDiscreteValuationRing» := P2M_GroundTheory_Heights__Heights_JacobianAtCurvePoint_exists_of_isDiscreteValuationRing_315fc3a6886b
