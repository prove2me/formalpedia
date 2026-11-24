-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_entry_eq
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.entry_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:10:59.390849+00:00
-- url     : https://prove2.me/theorems/7f2b9b80-d6d0-47bc-9d00-42b3e070fa5e
-- title:
--   Rank One Levi Identities: entry eq
-- statement:
--   The Rank One Levi Identities construction uses the entry eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HeisenbergDualBaseVectorFormulaAlt.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HeisenbergDualBaseVectorFormulaAlt.lean#L15-L16

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.entry_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) : M p q = (M *ᵥ bvec q) p := by sorry
