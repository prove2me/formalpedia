-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_herm_smul_r
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.BL.herm_smul_r
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:00:24.637883+00:00
-- url     : https://prove2.me/theorems/4e61c4fd-6769-5f34-964a-e422f08179c1
-- title:
--   BL: herm smul r
-- statement:
--   The BL construction uses the herm smul r property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/InvSqrtTwoMulSelf.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/InvSqrtTwoMulSelf.lean#L41-L43

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MatExtBvec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InvSqrtTwoMulSelf
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
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.Xi.BL.herm_smul_r (H : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (v w : Fin n → ℂ) :
    herm H v (c • w) = star c * herm H v w := by sorry
