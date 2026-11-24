-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_cs_le
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.cs_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T15:54:09.419825+00:00
-- url     : https://prove2.me/theorems/bd8f86a4-3ffc-4ed5-8e1d-61e644574c1e
-- title:
--   Rank One Levi Identities: cs le
-- statement:
--   The Rank One Levi Identities construction uses the cs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HeisenbergDualBaseVectorFormulaAlt.lean#L136-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HeisenbergDualBaseVectorFormulaAlt.lean#L136-L144

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormBaseVectorRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergDualBaseVectorFormulaAlt
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
open scoped ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r' : ℕ)

theorem ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.cs_le (c : ℂ) (x : HPar k r') (M : Mat k (1 + r'))
    (h : M ⟨2 * (1 + r') + k, by omega⟩ ⟨2 * (1 + r') + k, by omega⟩ = c * hb k r' x.1 x.2) :
    ‖c‖ * |x.2| ≤ gN M := by sorry
