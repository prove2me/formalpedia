-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_hpk_out
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.BL.hpk_out
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:56:18.883346+00:00
-- url     : https://prove2.me/theorems/20927383-703c-5ccd-ab5f-cad0bd64ffc0
-- title:
--   BL: hpk out
-- statement:
--   The BL construction uses the hpk out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermitianFormLiftVecFirstVector.lean#L42-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermitianFormLiftVecFirstVector.lean#L42-L47

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LevelDeterminantOfTriangularChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormLiftVecFirstVector
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
open scoped ENNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.BL
variable {k r' : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.Xi.BL.hpk_out (p : Fin (2 * (1 + r') + k + 1)) (hp : p.val = 0 ∨ p.val = 2 * (1 + r') + k)
    (q : Fin (2 * r' + k + 1)) : Hpk k (1 + r') p (sh q) = 0 := by sorry
