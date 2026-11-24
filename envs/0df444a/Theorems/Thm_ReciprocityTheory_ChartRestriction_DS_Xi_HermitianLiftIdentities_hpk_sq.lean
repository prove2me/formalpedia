-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_hpk_sq
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities.hpk_sq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:30:01.144262+00:00
-- url     : https://prove2.me/theorems/007f53a8-5106-4307-9532-7f1d45484edb
-- title:
--   Hermitian Lift Identities: hpk sq
-- statement:
--   The Hermitian Lift Identities construction uses the hpk sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HpkMulVecMulVec.lean#L100-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HpkMulVecMulVec.lean#L100-L101

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
variable (k r : ℕ)

theorem ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities.hpk_sq : Hpk k r * Hpk k r = 1 := by sorry
