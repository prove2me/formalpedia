-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_MinorPolynomials_shape_flatMap__3b9f0dcdf734
-- name    : P2M_Formalism_FourierDecayAlt_P_MinorPolynomials_shape_flatMap__3b9f0dcdf734
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:27:48.448535+00:00
-- url     : https://prove2.me/theorems/6a9a4991-c402-4792-b93d-4d902a18e48c
-- title:
--   P2 M Formalism Fourier Decay Alt P Minor Polynomials shape flat Map  3b9f0dcdf734: P2 M Formalism Fourier Decay Alt P Minor Polynomials shape flat Map  3b9f0dcdf734
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Minor Polynomials shape flat Map  3b9f0dcdf734 construction uses the P2 M Formalism Fourier Decay Alt P Minor Polynomials shape flat Map  3b9f0dcdf734 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IsOpenBigCellSet.lean#L51-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IsOpenBigCellSet.lean#L51-L58

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtEpart
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenBigCellSet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MinorPolynomials
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem P2M_Formalism_FourierDecayAlt_P_MinorPolynomials_shape_flatMap__3b9f0dcdf734 (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (F : Mat k r → (Wq →L[ℂ] Wp)) (Lf : FS k r nf) (f : CT k r nf × List (Mat k r) → FS k r nf) (g : Mat k r) :
    shape D fib F (Lf.flatMap f) g = (Lf.map fun e => shape D fib F (f e) g).sum := by sorry

alias «Formalism».«FourierDecayAlt».«P».«MinorPolynomials».«shape_flatMap'» := P2M_Formalism_FourierDecayAlt_P_MinorPolynomials_shape_flatMap__3b9f0dcdf734
