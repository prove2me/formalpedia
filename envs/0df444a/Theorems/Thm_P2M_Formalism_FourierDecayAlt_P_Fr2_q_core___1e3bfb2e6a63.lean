-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr2_q_core___1e3bfb2e6a63
-- name    : P2M_Formalism_FourierDecayAlt_P_Fr2_q_core___1e3bfb2e6a63
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:56:03.041796+00:00
-- url     : https://prove2.me/theorems/3668e273-9d89-46f6-8022-11fbec4bef82
-- title:
--   P2 M Formalism Fourier Decay Alt P Fr2 q core   1e3bfb2e6a63: P2 M Formalism Fourier Decay Alt P Fr2 q core   1e3bfb2e6a63
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Fr2 q core   1e3bfb2e6a63 construction uses the P2 M Formalism Fourier Decay Alt P Fr2 q core   1e3bfb2e6a63 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleRecOfAdmissibleWord.lean#L547-L551
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleRecOfAdmissibleWord.lean#L547-L551

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleRecOfAdmissibleWord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Finset Formalism.FourierDecayAlt.I Formalism.FourierDecayAlt.P.Interlace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr2

theorem P2M_Formalism_FourierDecayAlt_P_Fr2_q_core___1e3bfb2e6a63 (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y : ℝ) (hl1 : 1 ≤ l) (hlk : l ≤ k)
    (h : Interlaces k u u' ρ) (hA : u' l + 2 ≤ -Y ∧ -Y ≤ u l - 2) :
    ∏ i ∈ Icc 1 k, ((Y - 1 + 1/2 + u i) * (Y - 1 + 1/2 + u' i)) < 0 := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Fr2».«q_core''» := P2M_Formalism_FourierDecayAlt_P_Fr2_q_core___1e3bfb2e6a63
