-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_sub_mul_tri
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities.sub_mul_tri
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:50:40.902484+00:00
-- url     : https://prove2.me/theorems/82f7c861-6bf3-561e-824b-dec272479742
-- title:
--   Hermitian Lift Identities: sub mul tri
-- statement:
--   The Hermitian Lift Identities construction uses the sub mul tri property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HpkMulVecMulVec.lean#L123-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HpkMulVecMulVec.lean#L123-L145

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities.sub_mul_tri {n m : ℕ} (h : m ≤ n) (A B : Matrix (Fin n) (Fin n) ℂ) (hB : B.BlockTriangular id) :
    (A * B).submatrix (Fin.castLE h) (Fin.castLE h) =
      A.submatrix (Fin.castLE h) (Fin.castLE h) * B.submatrix (Fin.castLE h) (Fin.castLE h) := by sorry
