-- Prove2me | Theorems.Thm_PI_MultFromLatWork_symD_set_inv
-- name    : PI.MultFromLatWork.symD_set_inv
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:39:58.502326+00:00
-- url     : https://prove2.me/theorems/264e0bd4-7a5e-5d06-a40b-397a4309086d
-- title:
--   Mult From Lat Work: sym D set inv
-- statement:
--   The Mult From Lat Work construction uses the sym D set inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeMultiplicity/EncardLeOfFinset.lean#L71-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeMultiplicity/EncardLeOfFinset.lean#L71-L107

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

theorem PI.MultFromLatWork.symD_set_inv {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) :
    {t | ∃ k X : Matrix (Fin n) (Fin n) ℂ, k ∈ Kset ε ∧ inP ε X ∧
      ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = k * NormedSpace.exp X ∧
      t = Real.sqrt (hs X)} ⊆
    {t | ∃ k X : Matrix (Fin n) (Fin n) ℂ, k ∈ Kset ε ∧ inP ε X ∧
      (((g⁻¹ : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
        k * NormedSpace.exp X ∧ t = Real.sqrt (hs X)} := by sorry
