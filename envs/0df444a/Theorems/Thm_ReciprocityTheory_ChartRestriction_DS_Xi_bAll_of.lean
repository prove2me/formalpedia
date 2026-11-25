-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_bAll_of
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.bAll_of
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:49:37.108105+00:00
-- url     : https://prove2.me/theorems/ad05976d-8f6b-4376-8911-54b8233b19de
-- title:
--   Xi: b All of
-- statement:
--   The Xi construction uses the b All of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/XiExists2.lean#L15-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/XiExists2.lean#L15-L22

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_XiExists2
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem ReciprocityTheory.ChartRestriction.DS.Xi.bAll_of (hb : BStepBase) (hs : BStepSucc) :
    ∀ k r : ℕ, 1 ≤ k → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → BAt k r δ := by sorry
