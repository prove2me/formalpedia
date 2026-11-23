-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr2_q_core__291ef32df1e7
-- name    : P2M_Formalism_FourierDecayAlt_P_Fr2_q_core__291ef32df1e7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:41.828443+00:00
-- url     : https://prove2.me/theorems/04079fab-495f-4403-b576-7e0f74195f40
-- title:
--   P2 M Formalism Fourier Decay Alt P Fr2 q core  291ef32df1e7: P2 M Formalism Fourier Decay Alt P Fr2 q core  291ef32df1e7
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Fr2 q core  291ef32df1e7 construction uses the P2 M Formalism Fourier Decay Alt P Fr2 q core  291ef32df1e7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleRecOfAdmissibleWord.lean#L523-L545
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleRecOfAdmissibleWord.lean#L523-L545

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

theorem P2M_Formalism_FourierDecayAlt_P_Fr2_q_core__291ef32df1e7 (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y : ℝ) (hl1 : 1 ≤ l) (hlk : l ≤ k)
    (h : Interlaces k u u' ρ) (hA : u l + 2 ≤ -Y ∧ -Y ≤ u' l - 2) :
    ∏ i ∈ Icc 1 k, ((Y - 1 + 1/2 + u i) * (Y - 1 + 1/2 + u' i)) < 0 := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Fr2».«q_core'» := P2M_Formalism_FourierDecayAlt_P_Fr2_q_core__291ef32df1e7
