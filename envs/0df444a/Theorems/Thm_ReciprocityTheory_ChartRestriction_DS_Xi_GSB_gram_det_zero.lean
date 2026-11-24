-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GSB_gram_det_zero
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.GSB.gram_det_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:54:00.269859+00:00
-- url     : https://prove2.me/theorems/07628513-5bd8-4007-8fdf-81b275a857a7
-- title:
--   GSB: gram det zero
-- statement:
--   The GSB construction uses the gram det zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/GramReDetLe.lean#L14-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/GramReDetLe.lean#L14-L28

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LinIndToLp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GramReDetLe
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.GSB
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B ReciprocityTheory.ChartRestriction.DS.Xi.GS
variable {n m : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.Xi.GSB.gram_det_zero (w : Fin m → EuclideanSpace ℂ (Fin n)) (hw : ¬ LinearIndependent ℂ w) :
    (GS.gram w).det = 0 := by sorry
