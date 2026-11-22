-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_tsupport_smul_subset__d2c1bc7b3def
-- name    : P2M_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_tsupport_smul_subset__d2c1bc7b3def
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:13:54.76283+00:00
-- url     : https://prove2.me/theorems/2612c6a8-0b87-456e-ae04-9018f8ba189b
-- title:
--   P2 M Formalism Fourier Decay Alt P Wirtinger Integration By Parts tsupport smul subset  d2c1bc7b3def: P2 M Formalism Fourier Decay Alt P Wirtinger Integration By Parts tsupport smul subset  d2c1bc7b3d
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Wirtinger Integration By Parts tsupport smul subset  d2c1bc7b3def construction uses the P2 M Formalism Fourier Decay Alt P Wirtinger Integration By Parts tsupport smul subset  d2c1bc7b3def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L34-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L34-L40

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
open Formalism.FourierDecayAlt.G MeasureTheory

theorem P2M_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_tsupport_smul_subset__d2c1bc7b3def {E V : Type*} [TopologicalSpace E]
    [NormedAddCommGroup V] [NormedSpace ℂ V] (φ : E → ℂ) (a : E → V) :
    tsupport (fun x => φ x • a x) ⊆ tsupport a := by sorry

alias «Formalism».«FourierDecayAlt».«P».«WirtingerIntegrationByParts».«tsupport_smul_subset'» := P2M_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_tsupport_smul_subset__d2c1bc7b3def
