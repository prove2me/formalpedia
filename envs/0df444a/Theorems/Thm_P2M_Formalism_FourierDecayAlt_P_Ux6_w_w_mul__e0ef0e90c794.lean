-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Ux6_w_w_mul__e0ef0e90c794
-- name    : P2M_Formalism_FourierDecayAlt_P_Ux6_w_w_mul__e0ef0e90c794
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:56:07.801175+00:00
-- url     : https://prove2.me/theorems/5242c2e6-9971-41e2-a2dc-21b838596133
-- title:
--   P2 M Formalism Fourier Decay Alt P Ux6 w w mul  e0ef0e90c794: P2 M Formalism Fourier Decay Alt P Ux6 w w mul  e0ef0e90c794
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Ux6 w w mul  e0ef0e90c794 construction uses the P2 M Formalism Fourier Decay Alt P Ux6 w w mul  e0ef0e90c794 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L130-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L130-L131

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

theorem P2M_Formalism_FourierDecayAlt_P_Ux6_w_w_mul__e0ef0e90c794 {n : ℕ} (M : Matrix (Fin j) (Fin n) ℂ) : G.wMat j * (G.wMat j * M) = M := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Ux6».«w_w_mul'» := P2M_Formalism_FourierDecayAlt_P_Ux6_w_w_mul__e0ef0e90c794
