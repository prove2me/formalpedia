-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_XI_inv_fix
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.XI.inv_fix
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:49:29.470347+00:00
-- url     : https://prove2.me/theorems/236eb0f9-f406-4272-8403-dc7ebd28ba63
-- title:
--   XI: inv fix
-- statement:
--   The XI construction uses the inv fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/GaNonneg.lean#L42-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/GaNonneg.lean#L42-L45

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GramReDetLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaNonneg
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
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.XI
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem ReciprocityTheory.ChartRestriction.DS.Xi.XI.inv_fix {k r : ℕ} {h : Mat k r} (hu : IsUnit h.det) {v : Fin (2 * r + k + 1) → ℂ} (hv : h *ᵥ v = v) :
    h⁻¹ *ᵥ v = v := by sorry
