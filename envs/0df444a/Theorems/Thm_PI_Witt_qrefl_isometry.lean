-- Prove2me | Theorems.Thm_PI_Witt_qrefl_isometry
-- name    : PI.Witt.qrefl_isometry
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:59:11.416631+00:00
-- url     : https://prove2.me/theorems/039d4995-1534-4568-a598-d5200286173a
-- title:
--   Witt: qrefl isometry
-- statement:
--   The Witt construction uses the qrefl isometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittDecomposition/OneVector.lean#L24-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittDecomposition/OneVector.lean#L24-L36

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittDecomposition_Anisotropic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittDecomposition_OneVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Witt
variable {K V : Type} [Field K] [StarRing K] [CharZero K] [AddCommGroup V] [Module K V]
  (B : V →ₗ⋆[K] V →ₗ[K] K)

theorem PI.Witt.qrefl_isometry (hB : ∀ x y, star (B x y) = B y x) (v : V) (a : K) (ha : a ≠ 0)
    (hv : B v v = a + star a) (z w : V) :
    B (qrefl B v a z) (qrefl B v a w) = B z w := by sorry
