-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_E2_bdd_sum__8f26d2801aec
-- name    : P2M_Formalism_FourierDecayAlt_P_E2_bdd_sum__8f26d2801aec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:35.487934+00:00
-- url     : https://prove2.me/theorems/d54fa8ac-cd59-492c-acca-1f0ed82d1787
-- title:
--   P2 M Formalism Fourier Decay Alt P E2 bdd sum  8f26d2801aec: P2 M Formalism Fourier Decay Alt P E2 bdd sum  8f26d2801aec
-- statement:
--   The P2 M Formalism Fourier Decay Alt P E2 bdd sum  8f26d2801aec construction uses the P2 M Formalism Fourier Decay Alt P E2 bdd sum  8f26d2801aec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MiddleThirdEstimate.lean#L76-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MiddleThirdEstimate.lean#L76-L81

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

theorem P2M_Formalism_FourierDecayAlt_P_E2_bdd_sum__8f26d2801aec {Λ ι : Type} (T : Finset ι) (f : ι → Λ → ℂ) (hf : ∀ i, Bdd (f i)) :
    Bdd (∑ i ∈ T, f i) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«E2».«bdd_sum'» := P2M_Formalism_FourierDecayAlt_P_E2_bdd_sum__8f26d2801aec
