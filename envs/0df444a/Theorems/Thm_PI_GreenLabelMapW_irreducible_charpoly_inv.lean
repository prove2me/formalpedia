-- Prove2me | Theorems.Thm_PI_GreenLabelMapW_irreducible_charpoly_inv
-- name    : PI.GreenLabelMapW.irreducible_charpoly_inv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:31:03.165403+00:00
-- url     : https://prove2.me/theorems/d007c648-fc23-42b6-8159-f21d29d682a6
-- title:
--   Green Label Map W: irreducible charpoly inv
-- statement:
--   The Green Label Map W construction uses the irreducible charpoly inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelCharpoly/IrreducibleCharpolyInv.lean#L124-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelCharpoly/IrreducibleCharpolyInv.lean#L124-L147

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

theorem PI.GreenLabelMapW.irreducible_charpoly_inv {ι : Type} [Fintype ι] [DecidableEq ι] (γ : GL ι K)
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix ι ι K))) {z : AlgebraicClosure K}
    (hz0 : z ≠ 0) (hz : aeval z (Matrix.charpoly (γ : Matrix ι ι K)) = 0) :
    Irreducible (Matrix.charpoly ((γ⁻¹ : GL ι K) : Matrix ι ι K)) := by sorry
