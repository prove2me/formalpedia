-- Prove2me | Theorems.Thm_PI_WAU_sigmaFinite_of_K
-- name    : PI.WAU.sigmaFinite_of_K
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:11:25.933565+00:00
-- url     : https://prove2.me/theorems/152afde4-a6fc-4a91-86b1-84946d833bd3
-- title:
--   WAU: sigma Finite of K
-- statement:
--   The WAU construction uses the sigma Finite of K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/ConstructionD.lean#L23-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/ConstructionD.lean#L23-L37

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_KCountable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularIndex_PairwiseDisjointCosets
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ConstructionD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU
open Formalism.MainNotions.S MeasureTheory Matrix Pointwise

theorem PI.WAU.sigmaFinite_of_K (I : AutInst) (μ : Measure I.Gf) (hμ : μ.IsHaarMeasure)
    (hKc : IsCompact I.Kset) (hQ : ∃ s : Set I.Gf, s.Countable ∧ ∀ x : I.Gf, ∃ y ∈ s, y⁻¹ * x ∈ I.Kset) :
    SigmaFinite μ := by sorry
