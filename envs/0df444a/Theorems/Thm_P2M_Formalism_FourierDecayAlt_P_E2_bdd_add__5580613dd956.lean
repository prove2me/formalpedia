-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_E2_bdd_add__5580613dd956
-- name    : P2M_Formalism_FourierDecayAlt_P_E2_bdd_add__5580613dd956
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:13:31.282332+00:00
-- url     : https://prove2.me/theorems/0691b23d-37d2-4033-b9da-07b7352d6840
-- title:
--   P2 M Formalism Fourier Decay Alt P E2 bdd add  5580613dd956: P2 M Formalism Fourier Decay Alt P E2 bdd add  5580613dd956
-- statement:
--   The P2 M Formalism Fourier Decay Alt P E2 bdd add  5580613dd956 construction uses the P2 M Formalism Fourier Decay Alt P E2 bdd add  5580613dd956 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MiddleThirdEstimate.lean#L64-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MiddleThirdEstimate.lean#L64-L66

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MiddleThirdEstimate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.E2
open Formalism.FourierDecayAlt.E Real Polynomial MeasureTheory

theorem P2M_Formalism_FourierDecayAlt_P_E2_bdd_add__5580613dd956 {Λ : Type} {f g : Λ → ℂ} (hf : Bdd f) (hg : Bdd g) : Bdd (f + g) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«E2».«bdd_add'» := P2M_Formalism_FourierDecayAlt_P_E2_bdd_add__5580613dd956
