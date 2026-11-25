-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_block_eq
-- name    : ReciprocityTheory.AnForm.M.block_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:42:03.553062+00:00
-- url     : https://prove2.me/theorems/517da1e0-9c1f-4a03-97fa-b2d50d3f7e59
-- title:
--   M: block eq
-- statement:
--   The M construction uses the block eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ProdProofA.lean#L57-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ProdProofA.lean#L57-L63

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_FubiniStudyPotentialProductIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ProdProofA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory Matrix Filter Topology
open scoped ContDiff
noncomputable section
variable {e e' : ℕ}

theorem ReciprocityTheory.AnForm.M.block_eq (M1 : Matrix (Fin e) (Fin e) ℂ) (M2 : Matrix (Fin e') (Fin e') ℂ) :
    (J1 e e')ᵀ * M1 * J1 e e' + (J2 e e')ᵀ * M2 * J2 e e' =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks M1 0 0 M2) := by sorry
