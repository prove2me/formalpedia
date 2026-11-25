-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_prod_Iic_castLE
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.GS.prod_Iic_castLE
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:56:26.330629+00:00
-- url     : https://prove2.me/theorems/2922b86d-5f4b-5d1a-9ab4-f41852d917b3
-- title:
--   GS: prod Iic cast LE
-- statement:
--   The GS construction uses the prod Iic cast LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/ProdIicCastLE.lean#L49-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/ProdIicCastLE.lean#L49-L59

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ExistsKmat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ProdIicCastLE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.GS
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
variable {k r : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.Xi.GS.prod_Iic_castLE (l : Fin (r + 1)) (g : Fin (r + 1) → ℝ) :
    ∏ j ∈ Finset.Iic l, g j = ∏ j : Fin (l.val + 1), g (Fin.castLE (by omega) j) := by sorry
