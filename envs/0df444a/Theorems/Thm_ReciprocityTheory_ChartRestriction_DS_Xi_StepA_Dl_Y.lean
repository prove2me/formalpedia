-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_Dl_Y
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.StepA.Dl_Y
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:53:36.829451+00:00
-- url     : https://prove2.me/theorems/07a61478-a11c-4f5d-ace8-9de7f43e762a
-- title:
--   Step A: Dl Y
-- statement:
--   The Step A construction uses the Dl Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/DetEqMulMinorOfColZero.lean#L427-L443
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/DetEqMulMinorOfColZero.lean#L427-L443

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GoodRowsProjectorApplyEqSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_DetEqMulMinorOfColZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r' : ℕ)

theorem ReciprocityTheory.ChartRestriction.DS.Xi.StepA.Dl_Y (c : ℂ) (g : Mat k r') (l : Fin (1 + r' + 1)) :
    Dl k (1 + r') l (w0 k r' c * ιLev k 1 r' g) =
      c * (Matrix.of fun a b : Fin l.val =>
        herm (Hpk k r') (g *ᵥ phiV' k r' ⟨b.val, by omega⟩) (phiV' k r' ⟨a.val, by omega⟩)).det := by sorry
