-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_axK__dd0248578f9d
-- name    : P2M_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_axK__dd0248578f9d
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:55:51.728829+00:00
-- url     : https://prove2.me/theorems/027b75b7-23be-4a60-8a8b-a615bbe8dae3
-- title:
--   P2 M Formalism Fourier Decay Alt P Recursion With Densities A1 ax K  dd0248578f9d: P2 M Formalism Fourier Decay Alt P Recursion With Densities A1 ax K  dd0248578f9d
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Recursion With Densities A1 ax K  dd0248578f9d construction uses the P2 M Formalism Fourier Decay Alt P Recursion With Densities A1 ax K  dd0248578f9d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionWithDensities.lean#L311-L322
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionWithDensities.lean#L311-L322

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TA Finset
open scoped ComplexConjugate InnerProductSpace
open Classical
variable {E : Type} [Field E] [DecidableEq E]

theorem P2M_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_axK__dd0248578f9d (D : TA.Data E) (Sg : ℕ → ℕ → Finset E) (Th) (hNZ : NZSg Sg) (hK : AxK D) :
    AxK (D' D Sg Th) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«RecursionWithDensities».«A1».«axK'» := P2M_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_axK__dd0248578f9d
