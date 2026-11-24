-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_TwoBlockPoint_pt_append__77a8e803be09
-- name    : P2M_Formalism_FourierDecayAlt_P_TwoBlockPoint_pt_append__77a8e803be09
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:02.416293+00:00
-- url     : https://prove2.me/theorems/22cdedf6-d251-4895-80a4-f597281b8030
-- title:
--   P2 M Formalism Fourier Decay Alt P Two Block Point pt append  77a8e803be09: P2 M Formalism Fourier Decay Alt P Two Block Point pt append  77a8e803be09
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Two Block Point pt append  77a8e803be09 construction uses the P2 M Formalism Fourier Decay Alt P Two Block Point pt append  77a8e803be09 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwoBlockPoint.lean#L518-L522
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwoBlockPoint.lean#L518-L522

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
variable {K : Type} [CommRing K]

theorem P2M_Formalism_FourierDecayAlt_P_TwoBlockPoint_pt_append__77a8e803be09 (L l l' : List ℕ) (hL : L = l ++ l') (T T₁ T₂ : ℕ → Kˣ)
    (h₁ : ∀ b, b < l.length → T b = T₁ b) (h₂ : ∀ b, b < l'.length → T (l.length + b) = T₂ b)
    (hN : L.sum = l.sum + l'.sum) : pt L T = blkM hN (pt l T₁) 0 0 (pt l' T₂) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«TwoBlockPoint».«pt_append'» := P2M_Formalism_FourierDecayAlt_P_TwoBlockPoint_pt_append__77a8e803be09
