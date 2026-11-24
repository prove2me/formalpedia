-- Prove2me | Theorems.Thm_PI_GreenLabelMapW_root_inv
-- name    : PI.GreenLabelMapW.root_inv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:50.670804+00:00
-- url     : https://prove2.me/theorems/00693e85-f68f-428e-887e-a43196edbd39
-- title:
--   Green Label Map W: root inv
-- statement:
--   The Green Label Map W construction uses the root inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelCharpoly/IrreducibleCharpolyInv.lean#L100-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelCharpoly/IrreducibleCharpolyInv.lean#L100-L122

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_RootPowCard
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_IrreducibleCharpolyInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
noncomputable section
open PI PI.GreenLabelMapW
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem PI.GreenLabelMapW.root_inv {ι : Type} [Fintype ι] [DecidableEq ι] (γ : GL ι K) {z : AlgebraicClosure K}
    (hz0 : z ≠ 0) (hz : aeval z (Matrix.charpoly (γ : Matrix ι ι K)) = 0) :
    aeval z⁻¹ (Matrix.charpoly ((γ⁻¹ : GL ι K) : Matrix ι ι K)) = 0 := by sorry
