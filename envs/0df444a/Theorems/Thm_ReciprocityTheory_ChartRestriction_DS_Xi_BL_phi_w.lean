-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_phi_w
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.BL.phi_w
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:27:04.090525+00:00
-- url     : https://prove2.me/theorems/de26bfc6-793d-4c8f-82ae-f77e769ae1a1
-- title:
--   BL: phi w
-- statement:
--   The BL construction uses the phi w property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermExpand.lean#L70-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermExpand.lean#L70-L90

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.BL.phi_w (a : Fin (n + 1)) (i : Fin (k - 1)) : phiV k n a (wp k n i) = 0 := by sorry
