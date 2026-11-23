-- Prove2me | Theorems.Thm_PI_SqPairW_ringInt_smul
-- name    : PI.SqPairW.ringInt_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:04:18.473918+00:00
-- url     : https://prove2.me/theorems/2cfca0c4-12c7-4c81-970f-440c34a2ba9c
-- title:
--   Sq Pair W: ring Int smul
-- statement:
--   The Sq Pair W construction uses the ring Int smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairGluing/ExistsDenLe.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairGluing/ExistsDenLe.lean#L13-L15

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairGluing_ConjTransposeMemLam
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairGluing_ExistsDenLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairW
open Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}

theorem PI.SqPairW.ringInt_smul (β : 𝓞 E) (w : Fin N → E) : β • w = (β : E) • w := by sorry
