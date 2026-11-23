-- Prove2me | Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_xxw_mem_Ufl
-- name    : PI.TwistedEisensteinNonvanishing.W.xxw_mem_Ufl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:22:14.819807+00:00
-- url     : https://prove2.me/theorems/52d8c019-d2d8-4d73-b9fc-841ee6077249
-- title:
--   W: xxw mem Ufl
-- statement:
--   The W construction uses the xxw mem Ufl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/FreeCoordinateAffineInvertible.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/FreeCoordinateAffineInvertible.lean#L25-L27

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_FreeCoordinateAffineInvertible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE
variable {E : Type} [Field E]

theorem PI.TwistedEisensteinNonvanishing.W.xxw_mem_Ufl {n c i : ℕ} (v : Fin (n + c) → E) : v ∈ Ufl E n c i ↔ ∀ l : Fin (n + c), n + i ≤ l.1 → v l = 0 := by sorry
