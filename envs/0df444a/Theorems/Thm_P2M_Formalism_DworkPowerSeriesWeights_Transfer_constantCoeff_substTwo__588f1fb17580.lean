-- Prove2me | Theorems.Thm_P2M_Formalism_DworkPowerSeriesWeights_Transfer_constantCoeff_substTwo__588f1fb17580
-- name    : P2M_Formalism_DworkPowerSeriesWeights_Transfer_constantCoeff_substTwo__588f1fb17580
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:03:38.56042+00:00
-- url     : https://prove2.me/theorems/aabac3b1-44ee-43de-86d7-d6c743a4e33e
-- title:
--   P2 M Formalism Dwork Power Series Weights Transfer constant Coeff subst Two  588f1fb17580: P2 M Formalism Dwork Power Series Weights Transfer constant Coeff subst Two  588f1fb17580
-- statement:
--   The P2 M Formalism Dwork Power Series Weights Transfer constant Coeff subst Two  588f1fb17580 construction uses the P2 M Formalism Dwork Power Series Weights Transfer constant Coeff subst Two  588f1fb17580 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Transfer.lean#L42-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Transfer.lean#L42-L44

import Definitions.Def_Formalism_GaussJetBounds_FrameJetEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds MvPowerSeries
open Formalism.DworkPowerSeriesWeights.Transfer
variable {F K : Type} [Field F] [Field K] (φ : F →+* K) {d : ℕ}

theorem P2M_Formalism_DworkPowerSeriesWeights_Transfer_constantCoeff_substTwo__588f1fb17580 (s : ZMod d) : constantCoeff (s2' (K := F) s) = 0 := by sorry

alias «Formalism».«DworkPowerSeriesWeights».«Transfer».«constantCoeff_substTwo'» := P2M_Formalism_DworkPowerSeriesWeights_Transfer_constantCoeff_substTwo__588f1fb17580
