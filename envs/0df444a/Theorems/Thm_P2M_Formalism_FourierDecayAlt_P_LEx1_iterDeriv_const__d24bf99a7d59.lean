-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_LEx1_iterDeriv_const__d24bf99a7d59
-- name    : P2M_Formalism_FourierDecayAlt_P_LEx1_iterDeriv_const__d24bf99a7d59
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:55:36.630891+00:00
-- url     : https://prove2.me/theorems/cbb73ce4-fcae-49c2-9353-7333d72f3a17
-- title:
--   P2 M Formalism Fourier Decay Alt P LEx1 iter Deriv const  d24bf99a7d59: P2 M Formalism Fourier Decay Alt P LEx1 iter Deriv const  d24bf99a7d59
-- statement:
--   The P2 M Formalism Fourier Decay Alt P LEx1 iter Deriv const  d24bf99a7d59 construction uses the P2 M Formalism Fourier Decay Alt P LEx1 iter Deriv const  d24bf99a7d59 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LemmaEprimeFromSteps.lean#L358-L361
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LemmaEprimeFromSteps.lean#L358-L361

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaEprimeFromSteps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate

theorem P2M_Formalism_FourierDecayAlt_P_LEx1_iterDeriv_const__d24bf99a7d59 (p : ℕ) (k t : ℝ) : iteratedDeriv p (fun _ : ℝ => k) t = if p = 0 then k else 0 := by sorry

alias «Formalism».«FourierDecayAlt».«P».«LEx1».«iterDeriv_const'» := P2M_Formalism_FourierDecayAlt_P_LEx1_iterDeriv_const__d24bf99a7d59
