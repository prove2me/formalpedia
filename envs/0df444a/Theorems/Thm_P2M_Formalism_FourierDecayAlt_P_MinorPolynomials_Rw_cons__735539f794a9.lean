-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_MinorPolynomials_Rw_cons__735539f794a9
-- name    : P2M_Formalism_FourierDecayAlt_P_MinorPolynomials_Rw_cons__735539f794a9
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:11:38.266082+00:00
-- url     : https://prove2.me/theorems/54b57553-1070-49c7-ba52-65533e484fef
-- title:
--   P2 M Formalism Fourier Decay Alt P Minor Polynomials Rw cons  735539f794a9: P2 M Formalism Fourier Decay Alt P Minor Polynomials Rw cons  735539f794a9
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Minor Polynomials Rw cons  735539f794a9 construction uses the P2 M Formalism Fourier Decay Alt P Minor Polynomials Rw cons  735539f794a9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasDerivAtEpart.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasDerivAtEpart.lean#L17-L19

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtCvs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtEpart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MinorPolynomials
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem P2M_Formalism_FourierDecayAlt_P_MinorPolynomials_Rw_cons__735539f794a9 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (X : Mat k r) (w : List (Mat k r))
    (f : Mat k r → E) : Rw (X :: w) f = Dx (false, X) (Rw w f) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«MinorPolynomials».«Rw_cons'» := P2M_Formalism_FourierDecayAlt_P_MinorPolynomials_Rw_cons__735539f794a9
