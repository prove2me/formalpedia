-- Prove2me | Theorems.Thm_P2M_Formalism_DworkPowerSeriesWeights_Transfer_map_substOne__fd74c6d8f087
-- name    : P2M_Formalism_DworkPowerSeriesWeights_Transfer_map_substOne__fd74c6d8f087
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:54:35.374861+00:00
-- url     : https://prove2.me/theorems/ce23c9ff-05e6-4bbb-82c9-2dd3addd3f1e
-- title:
--   P2 M Formalism Dwork Power Series Weights Transfer map subst One  fd74c6d8f087: P2 M Formalism Dwork Power Series Weights Transfer map subst One  fd74c6d8f087
-- statement:
--   The P2 M Formalism Dwork Power Series Weights Transfer map subst One  fd74c6d8f087 construction uses the P2 M Formalism Dwork Power Series Weights Transfer map subst One  fd74c6d8f087 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Transfer.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Transfer.lean#L24-L26

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

theorem P2M_Formalism_DworkPowerSeriesWeights_Transfer_map_substOne__fd74c6d8f087 (s : ZMod d) : map φ (s1' (K := F) s) = s1' s := by sorry

alias «Formalism».«DworkPowerSeriesWeights».«Transfer».«map_substOne'» := P2M_Formalism_DworkPowerSeriesWeights_Transfer_map_substOne__fd74c6d8f087
