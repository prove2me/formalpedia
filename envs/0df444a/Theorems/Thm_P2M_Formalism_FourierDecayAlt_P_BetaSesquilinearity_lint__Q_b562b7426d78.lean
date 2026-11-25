-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_BetaSesquilinearity_lint__Q_b562b7426d78
-- name    : P2M_Formalism_FourierDecayAlt_P_BetaSesquilinearity_lint__Q_b562b7426d78
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:54:55.779809+00:00
-- url     : https://prove2.me/theorems/53878ce6-32e4-4185-aea0-bff180e4d54b
-- title:
--   P2 M Formalism Fourier Decay Alt P Beta Sesquilinearity lint  Q b562b7426d78: P2 M Formalism Fourier Decay Alt P Beta Sesquilinearity lint  Q b562b7426d78
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Beta Sesquilinearity lint  Q b562b7426d78 construction uses the P2 M Formalism Fourier Decay Alt P Beta Sesquilinearity lint  Q b562b7426d78 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaSesquilinearity.lean#L1128-L1138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaSesquilinearity.lean#L1128-L1138

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem P2M_Formalism_FourierDecayAlt_P_BetaSesquilinearity_lint__Q_b562b7426d78 (D : RealPlaceData k r Wp Wq) (f : (Fin r → ℂ) × ℂ → ℝ≥0∞) :
    ∫⁻ q, f q ∂μQ D = ∫⁻ q, ENNReal.ofReal (wt D q) * f q := by sorry

alias «Formalism».«FourierDecayAlt».«P».«BetaSesquilinearity».«lint_μQ» := P2M_Formalism_FourierDecayAlt_P_BetaSesquilinearity_lint__Q_b562b7426d78
