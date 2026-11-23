-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_A5x5_modK_mul__b5e25af6776b
-- name    : P2M_Formalism_FourierDecayAlt_P_A5x5_modK_mul__b5e25af6776b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:41:58.529809+00:00
-- url     : https://prove2.me/theorems/e37ec30e-8ed6-468e-bf40-a1a697fa85ae
-- title:
--   P2 M Formalism Fourier Decay Alt P A5x5 mod K mul  b5e25af6776b: P2 M Formalism Fourier Decay Alt P A5x5 mod K mul  b5e25af6776b
-- statement:
--   The P2 M Formalism Fourier Decay Alt P A5x5 mod K mul  b5e25af6776b construction uses the P2 M Formalism Fourier Decay Alt P A5x5 mod K mul  b5e25af6776b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelNonzeroModulusDeterminantEq.lean#L523-L526
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelNonzeroModulusDeterminantEq.lean#L523-L526

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x5
variable {K : Type} [CommRing K]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {R : Subring K}
variable [TopologicalSpace K] [IsTopologicalRing K] {ψ : AddChar K ℂ}

theorem P2M_Formalism_FourierDecayAlt_P_A5x5_modK_mul__b5e25af6776b (hd : LocalDatum K R ψ) {x y : K} (hx : IsUnit x) (hy : IsUnit y) :
    modK R (x * y) = modK R x * modK R y := by sorry

alias «Formalism».«FourierDecayAlt».«P».«A5x5».«modK_mul'» := P2M_Formalism_FourierDecayAlt_P_A5x5_modK_mul__b5e25af6776b
