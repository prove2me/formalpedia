-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_E2_lim_sum__192f31adbb3d
-- name    : P2M_Formalism_FourierDecayAlt_P_E2_lim_sum__192f31adbb3d
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:56:00.689764+00:00
-- url     : https://prove2.me/theorems/823db0d0-361e-4a98-b385-b850aa8d8b44
-- title:
--   P2 M Formalism Fourier Decay Alt P E2 lim sum  192f31adbb3d: P2 M Formalism Fourier Decay Alt P E2 lim sum  192f31adbb3d
-- statement:
--   The P2 M Formalism Fourier Decay Alt P E2 lim sum  192f31adbb3d construction uses the P2 M Formalism Fourier Decay Alt P E2 lim sum  192f31adbb3d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MiddleThirdEstimate.lean#L83-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MiddleThirdEstimate.lean#L83-L94

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

theorem P2M_Formalism_FourierDecayAlt_P_E2_lim_sum__192f31adbb3d {Λ ι : Type} (LIM : (Λ → ℂ) → ℂ)
    (h1 : ∀ f g, Bdd f → Bdd g → LIM (f + g) = LIM f + LIM g)
    (h2 : ∀ (c : ℂ) f, Bdd f → LIM (c • f) = c * LIM f)
    (T : Finset ι) (f : ι → Λ → ℂ) (hf : ∀ i, Bdd (f i)) :
    LIM (∑ i ∈ T, f i) = ∑ i ∈ T, LIM (f i) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«E2».«lim_sum'» := P2M_Formalism_FourierDecayAlt_P_E2_lim_sum__192f31adbb3d
