-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_LEx2_sq_nonneg__b7974ad0744f
-- name    : P2M_Formalism_FourierDecayAlt_P_LEx2_sq_nonneg__b7974ad0744f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:50:57.173625+00:00
-- url     : https://prove2.me/theorems/2ecec33b-ddf3-4059-a72e-db667eaec960
-- title:
--   P2 M Formalism Fourier Decay Alt P LEx2 sq nonneg  b7974ad0744f: P2 M Formalism Fourier Decay Alt P LEx2 sq nonneg  b7974ad0744f
-- statement:
--   The P2 M Formalism Fourier Decay Alt P LEx2 sq nonneg  b7974ad0744f construction uses the P2 M Formalism Fourier Decay Alt P LEx2 sq nonneg  b7974ad0744f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThetaLimit.lean#L437-L438
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThetaLimit.lean#L437-L438

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate

theorem P2M_Formalism_FourierDecayAlt_P_LEx2_sq_nonneg__b7974ad0744f (B : Base) {A' : Type} [Fintype A'] (wt : B.Ω → A' → ℝ) (hpos : ∀ ω a, 0 ≤ wt ω a) (v : Fn B A') (ω) :
    0 ≤ LE.sq B wt v ω := by sorry

alias «Formalism».«FourierDecayAlt».«P».«LEx2».«sq_nonneg'» := P2M_Formalism_FourierDecayAlt_P_LEx2_sq_nonneg__b7974ad0744f
