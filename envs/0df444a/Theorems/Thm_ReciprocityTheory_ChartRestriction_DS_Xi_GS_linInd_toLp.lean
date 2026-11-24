-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_linInd_toLp
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.GS.linInd_toLp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T15:53:45.627577+00:00
-- url     : https://prove2.me/theorems/bfbe0dd1-a4f6-470b-aaf7-e8d80a6ec87c
-- title:
--   GS: lin Ind to Lp
-- statement:
--   The GS construction uses the lin Ind to Lp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/LinIndToLp.lean#L81-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/LinIndToLp.lean#L81-L83

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LinIndToLp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix InnerProductSpace
open scoped ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.GS
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
variable {n m : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.Xi.GS.linInd_toLp {ι : Type*} (Y : ι → Fin n → ℂ) (hY : LinearIndependent ℂ Y) :
    LinearIndependent ℂ (fun a => (WithLp.toLp 2 (Y a) : EuclideanSpace ℂ (Fin n))) := by sorry
