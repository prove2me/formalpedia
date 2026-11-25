-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Ux6_wMat_mul_apply__b0bdc8c54c6d
-- name    : P2M_Formalism_FourierDecayAlt_P_Ux6_wMat_mul_apply__b0bdc8c54c6d
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:56:00.057569+00:00
-- url     : https://prove2.me/theorems/950bfbe3-a225-47f5-b7da-63e95cfd7bf4
-- title:
--   P2 M Formalism Fourier Decay Alt P Ux6 w Mat mul apply  b0bdc8c54c6d: P2 M Formalism Fourier Decay Alt P Ux6 w Mat mul apply  b0bdc8c54c6d
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Ux6 w Mat mul apply  b0bdc8c54c6d construction uses the P2 M Formalism Fourier Decay Alt P Ux6 w Mat mul apply  b0bdc8c54c6d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L176-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L176-L178

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux6
variable {k j ρ : ℕ}

theorem P2M_Formalism_FourierDecayAlt_P_Ux6_wMat_mul_apply__b0bdc8c54c6d {n : ℕ} (M : Matrix (Fin j) (Fin n) ℂ) (a : Fin j) (b : Fin n) :
    (G.wMat j * M) a b = M a.rev b := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Ux6».«wMat_mul_apply'» := P2M_Formalism_FourierDecayAlt_P_Ux6_wMat_mul_apply__b0bdc8c54c6d
