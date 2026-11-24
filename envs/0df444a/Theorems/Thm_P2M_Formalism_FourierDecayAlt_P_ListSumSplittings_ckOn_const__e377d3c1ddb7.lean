-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_ListSumSplittings_ckOn_const__e377d3c1ddb7
-- name    : P2M_Formalism_FourierDecayAlt_P_ListSumSplittings_ckOn_const__e377d3c1ddb7
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:07:26.266353+00:00
-- url     : https://prove2.me/theorems/b396bf0b-b96f-4ac8-b134-340cab34b6b6
-- title:
--   P2 M Formalism Fourier Decay Alt P List Sum Splittings ck On const  e377d3c1ddb7: P2 M Formalism Fourier Decay Alt P List Sum Splittings ck On const  e377d3c1ddb7
-- statement:
--   The P2 M Formalism Fourier Decay Alt P List Sum Splittings ck On const  e377d3c1ddb7 construction uses the P2 M Formalism Fourier Decay Alt P List Sum Splittings ck On const  e377d3c1ddb7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ListSumSplittings.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ListSumSplittings.lean#L38-L41

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ListSumSplittings
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic Formalism.FourierDecayAlt.P.ListSumInequalities
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem P2M_Formalism_FourierDecayAlt_P_ListSumSplittings_ckOn_const__e377d3c1ddb7 {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] {m : ℕ∞} (c : F) :
    CkOn m (GV k r) (fun _ : Mat k r => c) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«ListSumSplittings».«ckOn_const'» := P2M_Formalism_FourierDecayAlt_P_ListSumSplittings_ckOn_const__e377d3c1ddb7
