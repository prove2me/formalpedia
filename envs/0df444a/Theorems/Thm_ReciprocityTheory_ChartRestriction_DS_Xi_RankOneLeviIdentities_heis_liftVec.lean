-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_heis_liftVec
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.heis_liftVec
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T15:53:48.841801+00:00
-- url     : https://prove2.me/theorems/c29968a5-49f6-49db-a62e-c744a1613e6f
-- title:
--   Rank One Levi Identities: heis lift Vec
-- statement:
--   The Rank One Levi Identities construction uses the heis lift Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HeisenbergDualBaseVectorFormulaAlt.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HeisenbergDualBaseVectorFormulaAlt.lean#L23-L27

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.heis_liftVec (hHA : HeisAct) (x : HPar k r') (z : Fin (2 * r' + k + 1) → ℂ) :
    heis0 k r' x *ᵥ liftVec k 1 r' z =
      liftVec k 1 r' z - herm (Hpk k (1 + r')) (liftVec k 1 r' z) (liftVec k 1 r' x.1) • e0 k r' := by sorry
