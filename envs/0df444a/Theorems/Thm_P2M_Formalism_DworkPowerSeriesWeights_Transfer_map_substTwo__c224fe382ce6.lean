-- Prove2me | Theorems.Thm_P2M_Formalism_DworkPowerSeriesWeights_Transfer_map_substTwo__c224fe382ce6
-- name    : P2M_Formalism_DworkPowerSeriesWeights_Transfer_map_substTwo__c224fe382ce6
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:54:43.142901+00:00
-- url     : https://prove2.me/theorems/bc3453ee-19f0-428f-9025-5adcaddc25ee
-- title:
--   P2 M Formalism Dwork Power Series Weights Transfer map subst Two  c224fe382ce6: P2 M Formalism Dwork Power Series Weights Transfer map subst Two  c224fe382ce6
-- statement:
--   The P2 M Formalism Dwork Power Series Weights Transfer map subst Two  c224fe382ce6 construction uses the P2 M Formalism Dwork Power Series Weights Transfer map subst Two  c224fe382ce6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Transfer.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Transfer.lean#L27-L29

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

theorem P2M_Formalism_DworkPowerSeriesWeights_Transfer_map_substTwo__c224fe382ce6 (s : ZMod d) : map φ (s2' (K := F) s) = s2' s := by sorry

alias «Formalism».«DworkPowerSeriesWeights».«Transfer».«map_substTwo'» := P2M_Formalism_DworkPowerSeriesWeights_Transfer_map_substTwo__c224fe382ce6
