-- Prove2me | Theorems.Thm_P2M_Formalism_DworkPowerSeriesWeights_Transfer_constantCoeff_substOne__6454fc9e7ded
-- name    : P2M_Formalism_DworkPowerSeriesWeights_Transfer_constantCoeff_substOne__6454fc9e7ded
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:03:39.607503+00:00
-- url     : https://prove2.me/theorems/13529673-fdb9-4b2d-8f62-d4e2f42c9369
-- title:
--   P2 M Formalism Dwork Power Series Weights Transfer constant Coeff subst One  6454fc9e7ded: P2 M Formalism Dwork Power Series Weights Transfer constant Coeff subst One  6454fc9e7ded
-- statement:
--   The P2 M Formalism Dwork Power Series Weights Transfer constant Coeff subst One  6454fc9e7ded construction uses the P2 M Formalism Dwork Power Series Weights Transfer constant Coeff subst One  6454fc9e7ded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Transfer.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Transfer.lean#L39-L41

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

theorem P2M_Formalism_DworkPowerSeriesWeights_Transfer_constantCoeff_substOne__6454fc9e7ded (s : ZMod d) : constantCoeff (s1' (K := F) s) = 0 := by sorry

alias «Formalism».«DworkPowerSeriesWeights».«Transfer».«constantCoeff_substOne'» := P2M_Formalism_DworkPowerSeriesWeights_Transfer_constantCoeff_substOne__6454fc9e7ded
