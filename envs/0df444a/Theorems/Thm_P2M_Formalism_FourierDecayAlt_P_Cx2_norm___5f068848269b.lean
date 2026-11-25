-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Cx2_norm___5f068848269b
-- name    : P2M_Formalism_FourierDecayAlt_P_Cx2_norm___5f068848269b
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:06:10.228904+00:00
-- url     : https://prove2.me/theorems/f36c1bc4-8038-5d1e-b869-5335f613afb0
-- title:
--   P2 M Formalism Fourier Decay Alt P Cx2 norm   5f068848269b: P2 M Formalism Fourier Decay Alt P Cx2 norm   5f068848269b
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Cx2 norm   5f068848269b construction uses the P2 M Formalism Fourier Decay Alt P Cx2 norm   5f068848269b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstNormRealNonneg.lean#L111-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstNormRealNonneg.lean#L111-L113

import Definitions.Def_Formalism_HermitianCurvature_StatementC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelZeroEstimateProduct
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstNormRealNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C NumberField MeasureTheory
open scoped ComplexOrder ComplexConjugate RealInnerProductSpace
noncomputable section
open Formalism.FourierDecayAlt.P.Cx2
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {Wp Wq : InfinitePlace E → Type} [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

theorem P2M_Formalism_FourierDecayAlt_P_Cx2_norm___5f068848269b (S : HidaSetting E Wp Wq) (v : Fin S.f) (t : E) : ‖S.σ v t‖ = S.pl v t := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Cx2».«norm_σ» := P2M_Formalism_FourierDecayAlt_P_Cx2_norm___5f068848269b
