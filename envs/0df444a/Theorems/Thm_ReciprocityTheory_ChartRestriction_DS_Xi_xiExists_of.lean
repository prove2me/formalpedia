-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_xiExists_of
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.xiExists_of
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:53:54.078815+00:00
-- url     : https://prove2.me/theorems/e889889e-17bf-510c-a36e-b655b0aeb59b
-- title:
--   Xi: xi Exists of
-- statement:
--   The Xi construction uses the xi Exists of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/XiExists2.lean#L24-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/XiExists2.lean#L24-L35

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.xiExists_of (hA : ∀ k r : ℕ, 1 ≤ k → AAt k r) (hB : ∀ k r : ℕ, 1 ≤ k → BAt k r (1 / 2))
    (hC : CoefStep) (hX : XiIntStep) : XiExists := by sorry
