-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_herm_linF
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.BL.herm_linF
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:54:34.885725+00:00
-- url     : https://prove2.me/theorems/72303c98-55a4-5547-ae78-8b6c76cb733e
-- title:
--   BL: herm lin F
-- statement:
--   The BL construction uses the herm lin F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermExpand.lean#L201-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermExpand.lean#L201-L210

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormLiftVecFirstVector
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermExpand
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
variable (k n : ℕ)

theorem ReciprocityTheory.ChartRestriction.DS.Xi.BL.herm_linF (hk : 1 ≤ k) (y w : Fin (2 * n + k + 1) → ℂ) (s : ℝ) :
    herm (Hpk k n) y w = linF (fun j => herm (Hpk k n) (phiV' k n (Fin.cast (by omega) j)) w)
      (fun j => herm (Hpk k n) (phiV k n (Fin.cast (by omega) j)) w) (fun i => herm (Hpk k n) (wv k n i) w)
      (hcoord k n (y, s)) := by sorry
