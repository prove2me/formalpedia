-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_left_inv_of_inUJ
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.left_inv_of_inUJ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:58:51.709899+00:00
-- url     : https://prove2.me/theorems/61322d2b-bb72-422c-8322-06d34571a856
-- title:
--   S7: left inv of in UJ
-- statement:
--   The S7 construction uses the left inv of in UJ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/IsClosedEmbeddingToM.lean#L63-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/IsClosedEmbeddingToM.lean#L63-L67

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsClosedEmbeddingToM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedEmbeddingToM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Topology MeasureTheory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.S7.left_inv_of_inUJ (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) :
    (Jm ε * gᴴ * Jm ε) * g = 1 := by sorry
