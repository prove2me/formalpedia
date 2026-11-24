-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_io_bvec_out
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.BL.io_bvec_out
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T15:17:50.426333+00:00
-- url     : https://prove2.me/theorems/1398b80a-032c-493b-a065-1091eb49650e
-- title:
--   BL: io bvec out
-- statement:
--   The BL construction uses the io bvec out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/MatExtBvec.lean#L135-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/MatExtBvec.lean#L135-L137

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MatExtBvec
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
variable {k r' : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.Xi.BL.io_bvec_out (g : Mat k r') (q : Fin (2 * (1 + r') + k + 1)) (hq : q.val = 0 ∨ q.val = 2 * (1 + r') + k) :
    ιLev k 1 r' g *ᵥ bvec q = bvec q := by sorry
