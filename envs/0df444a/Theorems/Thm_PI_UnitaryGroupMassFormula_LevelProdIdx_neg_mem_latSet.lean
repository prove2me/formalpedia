-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LevelProdIdx_neg_mem_latSet
-- name    : PI.UnitaryGroupMassFormula.LevelProdIdx.neg_mem_latSet
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:39:35.973055+00:00
-- url     : https://prove2.me/theorems/189ee552-f43d-4fab-a0ab-6286d47e8a3e
-- title:
--   Level Prod Idx: neg mem lat Set
-- statement:
--   The Level Prod Idx construction uses the neg mem lat Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelProductIndex/ZeroMemLatSet.lean#L34-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelProductIndex/ZeroMemLatSet.lean#L34-L39

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_ZeroMemLatSet
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LevelProdIdx
open Formalism.UG
variable {F E : Type} [Field F] [Field E] [Algebra F E] {n : ℕ}
variable {R : Type} [CommRing R] [Algebra F R] {O : Subring R} {k : ℕ} {G : Fin k → (Fin n → E)}

theorem PI.UnitaryGroupMassFormula.LevelProdIdx.neg_mem_latSet {y : Fin n → E ⊗[F] R} (hy : y ∈ latSet R O G) :
    -y ∈ latSet R O G := by sorry
