-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_gram_comb
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.GS.gram_comb
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T15:53:46.133884+00:00
-- url     : https://prove2.me/theorems/1393f8af-d697-4008-85b6-180809cea602
-- title:
--   GS: gram comb
-- statement:
--   The GS construction uses the gram comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/LinIndToLp.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/LinIndToLp.lean#L17-L23

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.GS.gram_comb (w : Fin m → EuclideanSpace ℂ (Fin n)) (τ : Matrix (Fin m) (Fin m) ℂ) :
    gram (fun a => ∑ b, τ b a • w b) = τᴴ * gram w * τ := by sorry
