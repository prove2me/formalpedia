-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ThFin_dot_unit
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ThFin.dot_unit
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:56:35.427367+00:00
-- url     : https://prove2.me/theorems/69409947-0cd5-5eda-844a-fd1fa12da888
-- title:
--   Th Fin: dot unit
-- statement:
--   The Th Fin construction uses the dot unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HpkNegMp.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HpkNegMp.lean#L30-L32

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Phi2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixOfPerp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormBaseVectorRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HpkNegMp
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
open ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ThFin

theorem ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ThFin.dot_unit {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ} (hU : Uᴴ * U = 1) (u v : Fin n → ℂ) :
    star (U *ᵥ u) ⬝ᵥ (U *ᵥ v) = star u ⬝ᵥ v := by sorry
