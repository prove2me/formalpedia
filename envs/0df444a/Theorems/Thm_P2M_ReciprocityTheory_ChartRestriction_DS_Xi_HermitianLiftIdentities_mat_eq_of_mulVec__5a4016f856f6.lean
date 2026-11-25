-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_mat_eq_of_mulVec__5a4016f856f6
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_mat_eq_of_mulVec__5a4016f856f6
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:14:29.547928+00:00
-- url     : https://prove2.me/theorems/a117a223-101d-48ea-8464-c9134bf2b517
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS Xi Hermitian Lift Identities mat eq of mul Vec  5a4016f856f6: P2 M Reciprocity Theory Chart Restriction DS Xi Hermitian Lift Identities mat eq of mul Vec
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS Xi Hermitian Lift Identities mat eq of mul Vec  5a4016f856f6 construction uses the P2 M Reciprocity Theory Chart Restriction DS Xi Hermitian Lift Identities mat eq of mul Vec  5a4016f856f6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HpkMulVecMulVec.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HpkMulVecMulVec.lean#L41-L43

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ProdIicCastLE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HpkMulVecMulVec
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)

theorem P2M_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_mat_eq_of_mulVec__5a4016f856f6 [DecidableEq ι] {A B : Matrix ι ι ℂ} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«Xi».«HermitianLiftIdentities».«mat_eq_of_mulVec'» := P2M_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_mat_eq_of_mulVec__5a4016f856f6
