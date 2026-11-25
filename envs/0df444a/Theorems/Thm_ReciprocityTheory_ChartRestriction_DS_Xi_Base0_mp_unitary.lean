-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_mp_unitary
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.Base0.mp_unitary
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:46:49.817516+00:00
-- url     : https://prove2.me/theorems/fc6e1253-c410-4ef5-8de7-1371132dd851
-- title:
--   Base0: mp unitary
-- statement:
--   The Base0 construction uses the mp unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/IntegrableUnitIndicator.lean#L86-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/IntegrableUnitIndicator.lean#L86-L116

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_IntegrableUnitIndicator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.Base0

theorem ReciprocityTheory.ChartRestriction.DS.Xi.Base0.mp_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] (h : Matrix ι ι ℂ) (hu : h.conjTranspose * h = 1) :
    MeasurePreserving (fun y : ι → ℂ => h.mulVec y) volume volume := by sorry
