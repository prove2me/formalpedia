-- Prove2me | Theorems.Thm_PI_MultFromLatWork_inP_conj
-- name    : PI.MultFromLatWork.inP_conj
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:36:55.171943+00:00
-- url     : https://prove2.me/theorems/babf9b0e-20c2-49a9-94a0-2f77fc1399fe
-- title:
--   Mult From Lat Work: in P conj
-- statement:
--   The Mult From Lat Work construction uses the in P conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeMultiplicity/EncardLeOfFinset.lean#L40-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeMultiplicity/EncardLeOfFinset.lean#L40-L60

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LatCountG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeMultiplicity_EncardLeOfFinset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ENNReal
noncomputable section
open PI PI.MultFromLatWork
open Formalism.REAL

theorem PI.MultFromLatWork.inP_conj {n : ℕ} {ε : Fin n → Bool} {k X : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    (hX : inP ε X) : inP ε (k * X * kᴴ) := by sorry
