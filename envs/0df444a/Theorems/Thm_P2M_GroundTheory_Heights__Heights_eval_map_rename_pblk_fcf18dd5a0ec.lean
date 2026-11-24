-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval_map_rename_pblk_fcf18dd5a0ec
-- name    : P2M_GroundTheory_Heights__Heights_eval_map_rename_pblk_fcf18dd5a0ec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:36.061798+00:00
-- url     : https://prove2.me/theorems/1340928a-e862-4e9f-850e-3cfa32c087e8
-- title:
--   P2 M Ground Theory Heights  Heights eval map rename pblk fcf18dd5a0ec: P2 M Ground Theory Heights  Heights eval map rename pblk fcf18dd5a0ec
-- statement:
--   The P2 M Ground Theory Heights  Heights eval map rename pblk fcf18dd5a0ec construction uses the P2 M Ground Theory Heights  Heights eval map rename pblk fcf18dd5a0ec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSheetParam.lean#L36-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSheetParam.lean#L36-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetParam
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeProjHyperplaneNull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetParam
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_mcPts_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix Filter Topology Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre segre mcPts
  IsMultiHomogIdeal mcPts_smul)
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_eval_map_rename_pblk_fcf18dd5a0ec (z' : (Σ k, PBlk n k) → ℂ) (g : MvPolynomial (Fin n) ℤ) :
    eval z' (map (Int.castRingHom ℂ) (rename (fun i : Fin n => (⟨(), i⟩ : Σ k, PBlk n k)) g)) =
      eval (fun i => z' ⟨(), i⟩) (map (Int.castRingHom ℂ) g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«eval_map_rename_pblk» := P2M_GroundTheory_Heights__Heights_eval_map_rename_pblk_fcf18dd5a0ec
