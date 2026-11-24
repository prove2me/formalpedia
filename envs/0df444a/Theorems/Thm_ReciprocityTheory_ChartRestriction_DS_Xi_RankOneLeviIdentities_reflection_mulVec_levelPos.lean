-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_reflection_mulVec_levelPos
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.reflection_mulVec_levelPos
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:00:14.082324+00:00
-- url     : https://prove2.me/theorems/02ee31ce-d95d-4c63-aa5b-308b7901669e
-- title:
--   Rank One Levi Identities: reflection mul Vec level Pos
-- statement:
--   The Rank One Levi Identities construction uses the reflection mul Vec level Pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermitianFormBaseVectorRight.lean#L210-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermitianFormBaseVectorRight.lean#L210-L219

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.reflection_mulVec_levelPos (c : ℂ) (u : Fin (2 * (1 + r') + k + 1) → ℂ) (i : Fin (2 * r' + k + 1)) :
    (w0 k r' c *ᵥ u) (levPos k 1 r' i) = u (levPos k 1 r' i) := by sorry
