-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_HermConj_exists_orthogonal_family
-- name    : PI.UnitaryGroupMassFormula.HermConj.exists_orthogonal_family
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:44:58.941909+00:00
-- url     : https://prove2.me/theorems/500dab73-6d92-4e89-89b5-b4ffef91bb74
-- title:
--   Herm Conj: exists orthogonal family
-- statement:
--   The Herm Conj construction uses the exists orthogonal family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianDiagonalization/ExistsOrthogonalFamily.lean#L56-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianDiagonalization/ExistsOrthogonalFamily.lean#L56-L112

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianDiagonalization_HermDiag
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianDiagonalization_ExistsOrthogonalFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.HermConj
open Matrix
variable {E : Type} [Field E]

theorem PI.UnitaryGroupMassFormula.HermConj.exists_orthogonal_family [CharZero E] (σ : E →+* E) :
    ∀ (k : ℕ) (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V],
      Module.finrank E V = k → ∀ h : V → V → E, IsHermForm σ h →
        ∃ v : Fin k → V, LinearIndependent E v ∧ ∀ i j, i ≠ j → h (v i) (v j) = 0 := by sorry
