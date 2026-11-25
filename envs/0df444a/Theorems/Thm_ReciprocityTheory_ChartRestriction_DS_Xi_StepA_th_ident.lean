-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_th_ident
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.StepA.th_ident
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:00:22.864819+00:00
-- url     : https://prove2.me/theorems/b615729b-2afb-5dfd-9370-842602462ee2
-- title:
--   Step A: th ident
-- statement:
--   The Step A construction uses the th ident property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/ExponentShiftEqLevelExponent.lean#L84-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/ExponentShiftEqLevelExponent.lean#L84-L108

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InnerCLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ExponentShiftEqLevelExponent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r' : ℕ)

theorem ReciprocityTheory.ChartRestriction.DS.Xi.StepA.th_ident (s : Fin (1 + r' + 1) → ℝ) (aw : ℝ) (x : HPar k r') (hG0 : 0 < Ga k (1 + r') 0 (Yx k r' x))
    (hGl : ∀ l, 0 ≤ Ga k (1 + r') l (Yx k r' x)) :
    ENNReal.ofReal (Psi k r' s x) * ENNReal.ofReal (Dx k r' x ^ (-(aw + 2))) =
      ∏ l, ENNReal.ofReal (Ga k (1 + r') l (Yx k r' x) ^
        (-(if l = 0 then aw + 2 - ∑ l' : Fin (r' + 1), s (sc r' l') else s l) / 2)) := by sorry
