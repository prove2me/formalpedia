-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_cz_ne
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.BL.cz_ne
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:55:18.325177+00:00
-- url     : https://prove2.me/theorems/25317a28-1508-5bd4-9837-7cb4100dd8ed
-- title:
--   BL: cz ne
-- statement:
--   The BL construction uses the cz ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/InnerBound.lean#L68-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/InnerBound.lean#L68-L81

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MpUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InnerBound
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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.BL.cz_ne {k n : ℕ} (hk : 1 ≤ k) (z1 : Fin (2 * n + k + 1) → ℂ) (hT : 0 < Tz k n z1) :
    herm (Hpk k n) (phiV k n ⟨0, by omega⟩) (fvec k n z1 ⟨0, by omega⟩) ≠ 0 := by sorry
