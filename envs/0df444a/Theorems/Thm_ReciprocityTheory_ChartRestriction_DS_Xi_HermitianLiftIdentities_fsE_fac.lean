-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_fsE_fac
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities.fsE_fac
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:30:32.268811+00:00
-- url     : https://prove2.me/theorems/eab497ef-9cdc-46b1-a08c-592b56578f97
-- title:
--   Hermitian Lift Identities: fs E fac
-- statement:
--   The Hermitian Lift Identities construction uses the fs E fac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HpkMulVecMulVec.lean#L228-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HpkMulVecMulVec.lean#L228-L234

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
variable {k r : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities.fsE_fac (s : Fin (r + 1) → ℝ) (g1 g2 : Mat k r) (c : Fin (r + 1) → ℝ≥0)
    (h : ∀ l, ‖Dl k r l g1‖₊ = c l * ‖Dl k r l g2‖₊) :
    FsE k r s g1 = (∏ l, ((c l : ℝ≥0∞)) ^ (-s l)) * FsE k r s g2 := by sorry
