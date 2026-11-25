-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DB_ga_mem
-- name    : PI.UnitaryGroupMassFormula.UsCost.DB.ga_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:04:51.55459+00:00
-- url     : https://prove2.me/theorems/689d4e44-e7ba-449f-8aab-1d353ba39ceb
-- title:
--   DB: ga mem
-- statement:
--   The DB construction uses the ga mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/DerivB.lean#L93-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/DerivB.lean#L93-L102

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_DerivA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_DerivB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.DB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.DA

theorem PI.UnitaryGroupMassFormula.UsCost.DB.ga_mem (hMem : SliceMem) (hRad : RadicalParam) {k p s ρ : ℕ} {σ : Equiv.Perm (Fin p)} {d : Fin p → ℂ}
    (hd : ∀ i, d i ≠ 0) (ξ : Xi k p s ρ σ) {Z : G.Mat s} {γ : B.Mat k ρ} (hZ : G.detM Z ≠ 0)
    (hγ : γ ∈ B.GV k ρ) : gaXi k ρ σ d ξ Z γ ∈ B.GV k (p + s + ρ) := by sorry
