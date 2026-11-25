-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_det_gram_tri
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.BL.det_gram_tri
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:46:59.120714+00:00
-- url     : https://prove2.me/theorems/a18c6f4c-af7d-5a8c-890b-3760423f571f
-- title:
--   BL: det gram tri
-- statement:
--   The BL construction uses the det gram tri property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/InvSqrtTwoMulSelf.lean#L198-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/InvSqrtTwoMulSelf.lean#L198-L207

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.BL.det_gram_tri {N L : ℕ} (Z : Fin L → Fin N → ℂ) (T : Matrix (Fin L) (Fin L) ℂ) (hT : T.BlockTriangular id) :
    (Matrix.of fun a b => star (∑ j, T j a • Z j) ⬝ᵥ ∑ j, T j b • Z j).det =
      (star (∏ j, T j j) * ∏ j, T j j) * (Matrix.of fun a b => star (Z a) ⬝ᵥ Z b).det := by sorry
