-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_rankOneMatrix_last_coord
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.rankOneMatrix_last_coord
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:00:55.219552+00:00
-- url     : https://prove2.me/theorems/571e14f9-cfa8-418d-a3ce-c8989c58d110
-- title:
--   Rank One Levi Identities: rank One Matrix last coord
-- statement:
--   The Rank One Levi Identities construction uses the rank One Matrix last coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermitianFormBaseVectorRight.lean#L221-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermitianFormBaseVectorRight.lean#L221-L230

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormBaseVectorRight
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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.rankOneMatrix_last_coord (c : ℂ) (u : Fin (2 * (1 + r') + k + 1) → ℂ) :
    (w0 k r' c *ᵥ u) ⟨2 * (1 + r') + k, by omega⟩ = c * u ⟨0, by omega⟩ := by sorry
