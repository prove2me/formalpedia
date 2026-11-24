-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_mat_eq_of_mulVec
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.StepA.mat_eq_of_mulVec
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:55:38.456354+00:00
-- url     : https://prove2.me/theorems/9ff3575e-2bb2-4760-aafe-048da5e0572b
-- title:
--   Step A: mat eq of mul Vec
-- statement:
--   The Step A construction uses the mat eq of mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/UHMulInv.lean#L43-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/UHMulInv.lean#L43-L45

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_UHMulInv
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
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)

theorem ReciprocityTheory.ChartRestriction.DS.Xi.StepA.mat_eq_of_mulVec [DecidableEq ι] {A B : Matrix ι ι ℂ} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by sorry
