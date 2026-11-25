-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_herm_w_l
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.BL.herm_w_l
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:00:29.146337+00:00
-- url     : https://prove2.me/theorems/f43e7e72-9a9e-4706-8282-b12ad013f0c1
-- title:
--   BL: herm w l
-- statement:
--   The BL construction uses the herm w l property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermExpand.lean#L96-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermExpand.lean#L96-L101

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.BL.herm_w_l (v : Fin (2 * n + k + 1) → ℂ) (i : Fin (k - 1)) : herm (Hpk k n) (wv k n i) v = star (v (wp k n i)) := by sorry
