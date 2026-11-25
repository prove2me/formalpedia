-- Prove2me | Theorems.Thm_QPK_Bru_bf_meas
-- name    : QPK.Bru.bf_meas
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:50:57.454263+00:00
-- url     : https://prove2.me/theorems/713f22dc-9391-45e1-81c0-9c16bde14903
-- title:
--   Bru: bf meas
-- statement:
--   The Bru construction uses the bf meas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/BruhatDecomposition.lean#L98-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/BruhatDecomposition.lean#L98-L103

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarExist
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_BruhatDecomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open QPK
open QPK.Bru
variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem QPK.Bru.bf_meas (μ : Measure G) [SFinite μ] (K : ℕ → Set G) (hK : ∀ n, IsClosed (K n)) :
    Measurable (bf μ K) := by sorry
