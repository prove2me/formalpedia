-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_phiV__app_229d361ad964
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_phiV__app_229d361ad964
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:25:37.536591+00:00
-- url     : https://prove2.me/theorems/10c17e16-9b74-42af-95a0-b6a9315c8a34
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS Xi Step A ea phi V  app 229d361ad964: P2 M Reciprocity Theory Chart Restriction DS Xi Step A ea phi V  app 229d361ad964
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS Xi Step A ea phi V  app 229d361ad964 construction uses the P2 M Reciprocity Theory Chart Restriction DS Xi Step A ea phi V  app 229d361ad964 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/LastBasisZero.lean#L382-L402
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/LastBasisZero.lean#L382-L402

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Phi2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LastBasisZero
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
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem P2M_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_phiV__app_229d361ad964 {k r : ℕ} (hk : 1 ≤ k) (b : Fin (r + 1)) (i : Fin (2 * r + k + 1)) :
    phiV' k r b i = if b.val < r then (if i.val = b.val then 1 else 0) else
      ((Real.sqrt 2)⁻¹ : ℂ) * ((if i.val = r then 1 else 0) - (if i.val = r + k then 1 else 0)) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«Xi».«StepA».«ea_phiV'_app» := P2M_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_phiV__app_229d361ad964
