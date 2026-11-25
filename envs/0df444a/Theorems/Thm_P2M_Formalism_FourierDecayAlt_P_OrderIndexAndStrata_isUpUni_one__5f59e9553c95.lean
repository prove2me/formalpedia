-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_OrderIndexAndStrata_isUpUni_one__5f59e9553c95
-- name    : P2M_Formalism_FourierDecayAlt_P_OrderIndexAndStrata_isUpUni_one__5f59e9553c95
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:57:29.976265+00:00
-- url     : https://prove2.me/theorems/92abd131-7055-46ee-9309-de03daa0b25c
-- title:
--   P2 M Formalism Fourier Decay Alt P Order Index And Strata is Up Uni one  5f59e9553c95: P2 M Formalism Fourier Decay Alt P Order Index And Strata is Up Uni one  5f59e9553c95
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Order Index And Strata is Up Uni one  5f59e9553c95 construction uses the P2 M Formalism Fourier Decay Alt P Order Index And Strata is Up Uni one  5f59e9553c95 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrderIndexAndStrata.lean#L176-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrderIndexAndStrata.lean#L176-L177

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrderIndexAndStrata
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrderIndexAndStrata
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni)
open Formalism.FourierDecayAlt.S3

theorem P2M_Formalism_FourierDecayAlt_P_OrderIndexAndStrata_isUpUni_one__5f59e9553c95 {A : Type} [CommRing A] {n : ℕ} : IsUpUni (1 : Matrix (Fin n) (Fin n) A) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«OrderIndexAndStrata».«isUpUni_one'» := P2M_Formalism_FourierDecayAlt_P_OrderIndexAndStrata_isUpUni_one__5f59e9553c95
