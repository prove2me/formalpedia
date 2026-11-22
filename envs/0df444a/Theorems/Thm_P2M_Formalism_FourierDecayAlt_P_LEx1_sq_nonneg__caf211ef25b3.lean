-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_LEx1_sq_nonneg__caf211ef25b3
-- name    : P2M_Formalism_FourierDecayAlt_P_LEx1_sq_nonneg__caf211ef25b3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:52:55.231528+00:00
-- url     : https://prove2.me/theorems/5ca55ee3-65cb-4a3a-a407-ca7c4f5ee43d
-- title:
--   P2 M Formalism Fourier Decay Alt P LEx1 sq nonneg  caf211ef25b3: P2 M Formalism Fourier Decay Alt P LEx1 sq nonneg  caf211ef25b3
-- statement:
--   The P2 M Formalism Fourier Decay Alt P LEx1 sq nonneg  caf211ef25b3 construction uses the P2 M Formalism Fourier Decay Alt P LEx1 sq nonneg  caf211ef25b3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LemmaEprimeFromSteps.lean#L438-L439
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LemmaEprimeFromSteps.lean#L438-L439

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

theorem P2M_Formalism_FourierDecayAlt_P_LEx1_sq_nonneg__caf211ef25b3 (B : Base) {A' : Type} [Fintype A'] (wt : B.Ω → A' → ℝ) (hpos : ∀ ω a, 0 ≤ wt ω a) (v : Fn B A') (ω) :
    0 ≤ LE.sq B wt v ω := by sorry

alias «Formalism».«FourierDecayAlt».«P».«LEx1».«sq_nonneg'» := P2M_Formalism_FourierDecayAlt_P_LEx1_sq_nonneg__caf211ef25b3
