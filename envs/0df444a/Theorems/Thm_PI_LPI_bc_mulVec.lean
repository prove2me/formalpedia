-- Prove2me | Theorems.Thm_PI_LPI_bc_mulVec
-- name    : PI.LPI.bc_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:37.111604+00:00
-- url     : https://prove2.me/theorems/c0e53dbb-b0ed-4001-bb57-6ee38e7f2723
-- title:
--   LPI: bc mul Vec
-- statement:
--   The LPI construction uses the bc mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelProductIndex/Development.lean#L58-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelProductIndex/Development.lean#L58-L65

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LevelProdIdx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
noncomputable section
open PI PI.LPI
open Formalism.UG

theorem PI.LPI.bc_mulVec {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (φ : A →+* B)
    (g : GL (Fin n) A) (y : Fin n → A) :
    (fun j => φ (((g : Matrix (Fin n) (Fin n) A) *ᵥ y) j)) =
      ((bc φ g : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) *ᵥ (fun j => φ (y j)) := by sorry
