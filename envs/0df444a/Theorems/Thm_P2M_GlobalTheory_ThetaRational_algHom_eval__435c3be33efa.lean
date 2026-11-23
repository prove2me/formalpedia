-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ThetaRational_algHom_eval__435c3be33efa
-- name    : P2M_GlobalTheory_ThetaRational_algHom_eval__435c3be33efa
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:45.209833+00:00
-- url     : https://prove2.me/theorems/c2f9595e-7096-4001-af6e-ae797c00b579
-- title:
--   P2 M Global Theory Theta Rational alg Hom eval  435c3be33efa: P2 M Global Theory Theta Rational alg Hom eval  435c3be33efa
-- statement:
--   The P2 M Global Theory Theta Rational alg Hom eval  435c3be33efa construction uses the P2 M Global Theory Theta Rational alg Hom eval  435c3be33efa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsIntegralAndRationalTheta.lean#L212-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsIntegralAndRationalTheta.lean#L212-L222

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsIntegralAndRationalTheta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real ContDiff
open GlobalTheory GlobalTheory.ThetaRational
variable {A : Type*} [CommRing A] [Algebra ℂ A] {n : ℕ}

theorem P2M_GlobalTheory_ThetaRational_algHom_eval__435c3be33efa (j : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A) (χ : A →ₐ[ℂ] ℂ)
    (r : Polynomial (MvPolynomial (Fin n) ℂ)) (a : A) :
    χ (r.eval₂ j.toRingHom a) =
      (r.map (MvPolynomial.eval fun i => χ (j (MvPolynomial.X i)))).eval (χ a) := by sorry

alias «GlobalTheory».«ThetaRational».«algHom_eval₂» := P2M_GlobalTheory_ThetaRational_algHom_eval__435c3be33efa
