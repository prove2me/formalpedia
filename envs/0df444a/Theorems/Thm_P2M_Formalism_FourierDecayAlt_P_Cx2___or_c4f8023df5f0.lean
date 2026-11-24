-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Cx2___or_c4f8023df5f0
-- name    : P2M_Formalism_FourierDecayAlt_P_Cx2___or_c4f8023df5f0
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:17:08.129695+00:00
-- url     : https://prove2.me/theorems/eaf64e06-08df-4f8a-9e36-ff9641e7113b
-- title:
--   P2 M Formalism Fourier Decay Alt P Cx2   or c4f8023df5f0: P2 M Formalism Fourier Decay Alt P Cx2   or c4f8023df5f0
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Cx2   or c4f8023df5f0 construction uses the P2 M Formalism Fourier Decay Alt P Cx2   or c4f8023df5f0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstNormRealNonneg.lean#L103-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstNormRealNonneg.lean#L103-L109

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

theorem P2M_Formalism_FourierDecayAlt_P_Cx2___or_c4f8023df5f0 (S : HidaSetting E Wp Wq) (v : Fin S.f) :
    S.σ v = (S.pl v).embedding ∨ ComplexEmbedding.conjugate (S.σ v) = (S.pl v).embedding := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Cx2».«σ_or» := P2M_Formalism_FourierDecayAlt_P_Cx2___or_c4f8023df5f0
