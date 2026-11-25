-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_MinorPolynomials_hasDerivAt_invpow__0b9fd55a1697
-- name    : P2M_Formalism_FourierDecayAlt_P_MinorPolynomials_hasDerivAt_invpow__0b9fd55a1697
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:56:33.789084+00:00
-- url     : https://prove2.me/theorems/3062279e-3e06-4d88-8083-2e88b9cb38c7
-- title:
--   P2 M Formalism Fourier Decay Alt P Minor Polynomials has Deriv At invpow  0b9fd55a1697: P2 M Formalism Fourier Decay Alt P Minor Polynomials has Deriv At invpow  0b9fd55a1697
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Minor Polynomials has Deriv At invpow  0b9fd55a1697 construction uses the P2 M Formalism Fourier Decay Alt P Minor Polynomials has Deriv At invpow  0b9fd55a1697 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasDerivAtInvpow.lean#L174-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasDerivAtInvpow.lean#L174-L186

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HsVecApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BudgetClassEstimate
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_HasDerivAtInvpow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_DegPderivMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Expand
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtInvpow
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
variable {k r : ℕ}

theorem P2M_Formalism_FourierDecayAlt_P_MinorPolynomials_hasDerivAt_invpow__0b9fd55a1697 {c : ℝ → ℂ} {c' : ℂ} (hc : HasDerivAt c c' 0) {a : ℕ} (h0 : a = 0 ∨ c 0 ≠ 0) :
    HasDerivAt (fun t => (c t)⁻¹ ^ a) (-(a : ℂ) * c' * (c 0)⁻¹ ^ (a + 1)) 0 := by sorry

alias «Formalism».«FourierDecayAlt».«P».«MinorPolynomials».«hasDerivAt_invpow'» := P2M_Formalism_FourierDecayAlt_P_MinorPolynomials_hasDerivAt_invpow__0b9fd55a1697
