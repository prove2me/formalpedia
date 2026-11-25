-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_HermitianFormRankFour_fix_c__73ded1355d45
-- name    : P2M_Formalism_FourierDecayAlt_P_HermitianFormRankFour_fix_c__73ded1355d45
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:37:40.404236+00:00
-- url     : https://prove2.me/theorems/48ed5739-89c6-442d-b0bb-5b257cdbc82d
-- title:
--   P2 M Formalism Fourier Decay Alt P Hermitian Form Rank Four fix c  73ded1355d45: P2 M Formalism Fourier Decay Alt P Hermitian Form Rank Four fix c  73ded1355d45
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Hermitian Form Rank Four fix c  73ded1355d45 construction uses the P2 M Formalism Fourier Decay Alt P Hermitian Form Rank Four fix c  73ded1355d45 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormRankFour.lean#L309-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormRankFour.lean#L309-L316

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormRankFour
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD
open Formalism.FourierDecayAlt.P.HermitianFormRankFour
variable {k r : ℕ}

theorem P2M_Formalism_FourierDecayAlt_P_HermitianFormRankFour_fix_c__73ded1355d45 {z : Fin (2 * r + k + 1) → ℂ} {h : Mx k r} (hh : h ∈ UWset k r z) (j : JJ r) :
    h *ᵥ cvec' k r z j = cvec' k r z j := by sorry

alias «Formalism».«FourierDecayAlt».«P».«HermitianFormRankFour».«fix_c'» := P2M_Formalism_FourierDecayAlt_P_HermitianFormRankFour_fix_c__73ded1355d45
