-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_gN_nonneg__66b44f5708a9
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_gN_nonneg__66b44f5708a9
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:38:42.050419+00:00
-- url     : https://prove2.me/theorems/a9f38713-1cee-49f3-9e52-5a05c5eb525d
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS Xi Rank One Levi Identities g N nonneg  66b44f5708a9: P2 M Reciprocity Theory Chart Restriction DS Xi Rank One Levi Identities g N nonneg  66b44f5708a9
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS Xi Rank One Levi Identities g N nonneg  66b44f5708a9 construction uses the P2 M Reciprocity Theory Chart Restriction DS Xi Rank One Levi Identities g N nonneg  66b44f5708a9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HeisenbergDualBaseVectorFormulaAlt.lean#L108-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HeisenbergDualBaseVectorFormulaAlt.lean#L108-L108

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_gN_nonneg__66b44f5708a9 {n : ℕ} (M : Mat k n) : 0 ≤ gN M := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«Xi».«RankOneLeviIdentities».«gN_nonneg'» := P2M_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_gN_nonneg__66b44f5708a9
