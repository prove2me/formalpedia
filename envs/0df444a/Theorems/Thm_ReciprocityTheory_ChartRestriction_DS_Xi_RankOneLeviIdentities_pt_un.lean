-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_pt_un
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.pt_un
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:00:57.156805+00:00
-- url     : https://prove2.me/theorems/d13eab08-ae9b-50cb-b869-7c78bcaad546
-- title:
--   Rank One Levi Identities: pt un
-- statement:
--   The Rank One Levi Identities construction uses the pt un property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HeisenbergDualBaseVectorFormulaAlt.lean#L157-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HeisenbergDualBaseVectorFormulaAlt.lean#L157-L166

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
variable (c : ℂ) (g : Mat k r') (x : HPar k r')

theorem ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.pt_un (hHA : HeisAct) :
    gN g ≤ gN (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ∧
      ‖c‖ * ‖x.1‖ ≤ gN (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ∧
      ‖c‖ * |x.2| ≤ gN (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) := by sorry
