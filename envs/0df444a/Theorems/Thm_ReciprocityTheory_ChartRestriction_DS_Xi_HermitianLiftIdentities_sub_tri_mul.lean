-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_sub_tri_mul
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities.sub_tri_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:50:12.189218+00:00
-- url     : https://prove2.me/theorems/f99addcc-93f2-556b-b304-076f3aa61c79
-- title:
--   Hermitian Lift Identities: sub tri mul
-- statement:
--   The Hermitian Lift Identities construction uses the sub tri mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HpkMulVecMulVec.lean#L147-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HpkMulVecMulVec.lean#L147-L169

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities.sub_tri_mul {n m : ℕ} (h : m ≤ n) (A B : Matrix (Fin n) (Fin n) ℂ) (hB : B.BlockTriangular id) :
    (Bᴴ * A).submatrix (Fin.castLE h) (Fin.castLE h) =
      (B.submatrix (Fin.castLE h) (Fin.castLE h))ᴴ * A.submatrix (Fin.castLE h) (Fin.castLE h) := by sorry
