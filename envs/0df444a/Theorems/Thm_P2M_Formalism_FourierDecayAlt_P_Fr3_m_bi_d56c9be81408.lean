-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr3_m_bi_d56c9be81408
-- name    : P2M_Formalism_FourierDecayAlt_P_Fr3_m_bi_d56c9be81408
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:00:20.569284+00:00
-- url     : https://prove2.me/theorems/ed7401ea-ed5f-43a6-8830-2ca73ec65d2a
-- title:
--   P2 M Formalism Fourier Decay Alt P Fr3 m bi d56c9be81408: P2 M Formalism Fourier Decay Alt P Fr3 m bi d56c9be81408
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Fr3 m bi d56c9be81408 construction uses the P2 M Formalism Fourier Decay Alt P Fr3 m bi d56c9be81408 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/L0ConstantPartCommute.lean#L61-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/L0ConstantPartCommute.lean#L61-L63

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L0ConstantPartCommute
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr3
variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r)

theorem P2M_Formalism_FourierDecayAlt_P_Fr3_m_bi_d56c9be81408 : L.ζbi ∈ zfns L := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Fr3».«mζbi» := P2M_Formalism_FourierDecayAlt_P_Fr3_m_bi_d56c9be81408
