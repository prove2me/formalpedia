-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B2x8_cf_heis__t_8476e10eaf02
-- name    : P2M_Formalism_FourierDecayAlt_P_B2x8_cf_heis__t_8476e10eaf02
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:55:17.197927+00:00
-- url     : https://prove2.me/theorems/88137666-f674-41da-998c-a89e8f4cfc6b
-- title:
--   P2 M Formalism Fourier Decay Alt P B2x8 cf heis  t 8476e10eaf02: P2 M Formalism Fourier Decay Alt P B2x8 cf heis  t 8476e10eaf02
-- statement:
--   The P2 M Formalism Fourier Decay Alt P B2x8 cf heis  t 8476e10eaf02 construction uses the P2 M Formalism Fourier Decay Alt P B2x8 cf heis  t 8476e10eaf02 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L1239-L1267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L1239-L1267

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

theorem P2M_Formalism_FourierDecayAlt_P_B2x8_cf_heis__t_8476e10eaf02 (x₀ : HPar k r') (p : ℂ × HPar k r') (h1 : p.1 ≠ 0) :
    heis0 k r' x₀ *ᵥ Ψt k r' p = Ψt k r' (Tn k r' x₀ p) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«B2x8».«cf_heis_Ψt» := P2M_Formalism_FourierDecayAlt_P_B2x8_cf_heis__t_8476e10eaf02
