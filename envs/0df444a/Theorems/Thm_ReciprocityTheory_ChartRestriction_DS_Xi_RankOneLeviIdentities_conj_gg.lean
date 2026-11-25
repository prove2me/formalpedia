-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_conj_gg
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.conj_gg
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:49:26.338204+00:00
-- url     : https://prove2.me/theorems/161aacb2-8419-4705-b590-57ce272acd2f
-- title:
--   Rank One Levi Identities: conj gg
-- statement:
--   The Rank One Levi Identities construction uses the conj gg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HeisenbergDualBaseVectorFormulaAlt.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HeisenbergDualBaseVectorFormulaAlt.lean#L38-L43

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.conj_gg (hHA : HeisAct) (i j : Fin (2 * r' + k + 1)) :
    (w0 k r' c * heis0 k r' x * ιLev k 1 r' g) (levPos k 1 r' i) (levPos k 1 r' j) = g i j := by sorry
