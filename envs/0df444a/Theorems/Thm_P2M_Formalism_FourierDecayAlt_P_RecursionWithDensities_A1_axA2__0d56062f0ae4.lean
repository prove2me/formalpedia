-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_axA2__0d56062f0ae4
-- name    : P2M_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_axA2__0d56062f0ae4
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:56:40.09155+00:00
-- url     : https://prove2.me/theorems/96ca341f-4568-4be8-b714-5aa7730073f0
-- title:
--   P2 M Formalism Fourier Decay Alt P Recursion With Densities A1 ax A2  0d56062f0ae4: P2 M Formalism Fourier Decay Alt P Recursion With Densities A1 ax A2  0d56062f0ae4
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Recursion With Densities A1 ax A2  0d56062f0ae4 construction uses the P2 M Formalism Fourier Decay Alt P Recursion With Densities A1 ax A2  0d56062f0ae4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionWithDensities.lean#L324-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionWithDensities.lean#L324-L329

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

theorem P2M_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_axA2__0d56062f0ae4 (D : TA.Data E) (Sg : ℕ → ℕ → Finset E) (Th) (hA : KernelSupport D) : KernelSupport (D' D Sg Th) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«RecursionWithDensities».«A1».«axA2'» := P2M_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_axA2__0d56062f0ae4
