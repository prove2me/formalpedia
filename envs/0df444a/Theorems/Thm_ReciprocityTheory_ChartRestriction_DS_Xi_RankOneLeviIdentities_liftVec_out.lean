-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_liftVec_out
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.liftVec_out
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:44:29.981805+00:00
-- url     : https://prove2.me/theorems/717d7a48-8764-480e-a8eb-c25856fe69fe
-- title:
--   Rank One Levi Identities: lift Vec out
-- statement:
--   The Rank One Levi Identities construction uses the lift Vec out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermitianFormBaseVectorRight.lean#L92-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermitianFormBaseVectorRight.lean#L92-L94

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.liftVec_out (z : Fin (2 * r' + k + 1) → ℂ) (p : Fin (2 * (1 + r') + k + 1))
    (h : p.val = 0 ∨ p.val = 2 * (1 + r') + k) : liftVec k 1 r' z p = 0 := by sorry
