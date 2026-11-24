-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_levelEmbedding_mulVec_es0
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.levelEmbedding_mulVec_es0
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:00:31.011544+00:00
-- url     : https://prove2.me/theorems/dc4628e1-3b42-4388-8265-58267ad6bbdb
-- title:
--   Rank One Levi Identities: level Embedding mul Vec es0
-- statement:
--   The Rank One Levi Identities construction uses the level Embedding mul Vec es0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermitianFormBaseVectorRight.lean#L202-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermitianFormBaseVectorRight.lean#L202-L203

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.levelEmbedding_mulVec_es0 (g : Mat k r') : ιLev k 1 r' g *ᵥ es0 k r' = es0 k r' := by sorry
