-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_JFxB_rho_eq_trn__db6dceb877d0
-- name    : P2M_Formalism_FourierDecayAlt_P_JFxB_rho_eq_trn__db6dceb877d0
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:00:42.360971+00:00
-- url     : https://prove2.me/theorems/d56f7fe7-70e6-44b8-8976-cbbd9a696452
-- title:
--   P2 M Formalism Fourier Decay Alt P JFx B rho eq trn  db6dceb877d0: P2 M Formalism Fourier Decay Alt P JFx B rho eq trn  db6dceb877d0
-- statement:
--   The P2 M Formalism Fourier Decay Alt P JFx B rho eq trn  db6dceb877d0 construction uses the P2 M Formalism Fourier Decay Alt P JFx B rho eq trn  db6dceb877d0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CvRhoOfParts.lean#L260-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CvRhoOfParts.lean#L260-L268

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxB
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem P2M_Formalism_FourierDecayAlt_P_JFxB_rho_eq_trn__db6dceb877d0 {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) (p : SS k r) (F : Mat k r → (Wq →L[ℂ] Wp)) :
    rho D p F = trn (Lq D p) ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹) (Matrix.of p.2.2 * Matrix.of p.2.1) F := by sorry

alias «Formalism».«FourierDecayAlt».«P».«JFxB».«rho_eq_trn'» := P2M_Formalism_FourierDecayAlt_P_JFxB_rho_eq_trn__db6dceb877d0
