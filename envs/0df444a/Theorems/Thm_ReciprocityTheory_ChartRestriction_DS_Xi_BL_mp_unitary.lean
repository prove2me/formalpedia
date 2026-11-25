-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_mp_unitary
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.BL.mp_unitary
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:47:36.46086+00:00
-- url     : https://prove2.me/theorems/7c10f0c5-ee80-53af-9ba3-01cb62b7aa49
-- title:
--   BL: mp unitary
-- statement:
--   The BL construction uses the mp unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/MpUnitary.lean#L65-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/MpUnitary.lean#L65-L78

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermExpand
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MpUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.BL

theorem ReciprocityTheory.ChartRestriction.DS.Xi.BL.mp_unitary {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (hU : Uᴴ * U = 1) :
    MeasurePreserving (fun y : Fin N → ℂ => U *ᵥ y) volume volume := by sorry
