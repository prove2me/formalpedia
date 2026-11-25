-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_D_symm
-- name    : ReciprocityTheory.ChartRestriction.DS.D_symm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:02:42.895615+00:00
-- url     : https://prove2.me/theorems/d27b685b-a56b-561d-a6c9-343336d8a089
-- title:
--   DS: D symm
-- statement:
--   The DS construction uses the D symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARUnit.lean#L168-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARUnit.lean#L168-L172

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CsqDdPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem ReciprocityTheory.ChartRestriction.DS.D_symm {ε : Fin n → Bool} {E cp cm : Fin n → Fin n → Module.End ℂ W} (hU : IsInfUnitary ε E)
    (hEC : CommutesCAR E cp cm) (hadj : ∀ (i a : Fin n) (x y : W), inner ℂ (cp i a x) y = inner ℂ x (cm i a y)) (x y : W) :
    inner ℂ ((dOp ε E cp + dOp' ε E cm) x) y = inner ℂ x ((dOp ε E cp + dOp' ε E cm) y) := by sorry
