-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_liftVec_apply
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.liftVec_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:44:29.456976+00:00
-- url     : https://prove2.me/theorems/0c22108b-b55a-4d87-8a69-a03720827379
-- title:
--   Rank One Levi Identities: lift Vec apply
-- statement:
--   The Rank One Levi Identities construction uses the lift Vec apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermitianFormBaseVectorRight.lean#L83-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermitianFormBaseVectorRight.lean#L83-L85

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.liftVec_apply (z : Fin (2 * r' + k + 1) → ℂ) (p : Fin (2 * (1 + r') + k + 1)) :
    liftVec k 1 r' z p = if h : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1 then z ⟨p.val - 1, by omega⟩ else 0 := by sorry
