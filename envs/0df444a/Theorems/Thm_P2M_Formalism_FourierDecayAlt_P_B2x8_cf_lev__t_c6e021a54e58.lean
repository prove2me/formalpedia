-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B2x8_cf_lev__t_c6e021a54e58
-- name    : P2M_Formalism_FourierDecayAlt_P_B2x8_cf_lev__t_c6e021a54e58
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:54:58.544793+00:00
-- url     : https://prove2.me/theorems/0b098b1a-6399-4a17-89a5-6346620c4c8d
-- title:
--   P2 M Formalism Fourier Decay Alt P B2x8 cf lev  t c6e021a54e58: P2 M Formalism Fourier Decay Alt P B2x8 cf lev  t c6e021a54e58
-- statement:
--   The P2 M Formalism Fourier Decay Alt P B2x8 cf lev  t c6e021a54e58 construction uses the P2 M Formalism Fourier Decay Alt P B2x8 cf lev  t c6e021a54e58 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L1234-L1237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L1234-L1237

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}

theorem P2M_Formalism_FourierDecayAlt_P_B2x8_cf_lev__t_c6e021a54e58 (g₁ : Mat k r') (hg : g₁ ∈ GV k r') (p : ℂ × HPar k r') :
    ιLev k 1 r' g₁ *ᵥ Ψt k r' p = Ψt k r' (Tl k r' g₁ p) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«B2x8».«cf_lev_Ψt» := P2M_Formalism_FourierDecayAlt_P_B2x8_cf_lev__t_c6e021a54e58
