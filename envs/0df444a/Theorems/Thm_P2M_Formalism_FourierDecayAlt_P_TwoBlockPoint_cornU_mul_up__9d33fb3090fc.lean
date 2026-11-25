-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_TwoBlockPoint_cornU_mul_up__9d33fb3090fc
-- name    : P2M_Formalism_FourierDecayAlt_P_TwoBlockPoint_cornU_mul_up__9d33fb3090fc
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:56:01.153168+00:00
-- url     : https://prove2.me/theorems/6b2a607c-1221-46c0-9d0a-08a7e5d21b3d
-- title:
--   P2 M Formalism Fourier Decay Alt P Two Block Point corn U mul up  9d33fb3090fc: P2 M Formalism Fourier Decay Alt P Two Block Point corn U mul up  9d33fb3090fc
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Two Block Point corn U mul up  9d33fb3090fc construction uses the P2 M Formalism Fourier Decay Alt P Two Block Point corn U mul up  9d33fb3090fc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwoBlockPoint.lean#L1046-L1060
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwoBlockPoint.lean#L1046-L1060

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_fib
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_gl_coe
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_left_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_m_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_mem_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_right_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism.FourierDecayAlt.P.A5x8 (sec_m sec_m_ext sec_gl sec_gl_coe sec_fib sec_right_eq sec_left_eq sec_mem_int toCos)
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoBlockPoint
variable {K : Type} [CommRing K] (R : Subring K)
variable {a s : ℕ}

theorem P2M_Formalism_FourierDecayAlt_P_TwoBlockPoint_cornU_mul_up__9d33fb3090fc {u : Matrix (Fin s) (Fin s) K} (hu : IsUpUni u) (Y : Matrix (Fin a) (Fin s) K) :
    cornU (Y * u) = cornU Y := by sorry

alias «Formalism».«FourierDecayAlt».«P».«TwoBlockPoint».«cornU_mul_up'» := P2M_Formalism_FourierDecayAlt_P_TwoBlockPoint_cornU_mul_up__9d33fb3090fc
