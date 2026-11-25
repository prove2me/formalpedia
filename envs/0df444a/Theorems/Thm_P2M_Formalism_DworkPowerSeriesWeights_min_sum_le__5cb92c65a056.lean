-- Prove2me | Theorems.Thm_P2M_Formalism_DworkPowerSeriesWeights_min_sum_le__5cb92c65a056
-- name    : P2M_Formalism_DworkPowerSeriesWeights_min_sum_le__5cb92c65a056
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:56:15.391928+00:00
-- url     : https://prove2.me/theorems/ca961831-8703-449b-8010-55015577bf3b
-- title:
--   P2 M Formalism Dwork Power Series Weights min sum le  5cb92c65a056: P2 M Formalism Dwork Power Series Weights min sum le  5cb92c65a056
-- statement:
--   The P2 M Formalism Dwork Power Series Weights min sum le  5cb92c65a056 construction uses the P2 M Formalism Dwork Power Series Weights min sum le  5cb92c65a056 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L187-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L187-L197

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FirstRowMinorDegreeLeOne
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
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open MvPolynomial

theorem P2M_Formalism_DworkPowerSeriesWeights_min_sum_le__5cb92c65a056 {σ : Type} [Fintype σ] (Pr : σ → Prop) [DecidablePred Pr] (u u' : σ →₀ ℕ) :
    (∑ y, min (u y) (u' y)) + ∑ y ∈ Finset.univ.filter Pr, u y ≤
      (∑ y ∈ Finset.univ.filter Pr, u' y) + ∑ y, u y := by sorry

alias «Formalism».«DworkPowerSeriesWeights».«min_sum_le'» := P2M_Formalism_DworkPowerSeriesWeights_min_sum_le__5cb92c65a056
