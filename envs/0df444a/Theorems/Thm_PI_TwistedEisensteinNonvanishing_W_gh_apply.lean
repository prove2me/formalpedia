-- Prove2me | Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_gh_apply
-- name    : PI.TwistedEisensteinNonvanishing.W.gh_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:42:18.128257+00:00
-- url     : https://prove2.me/theorems/7122a710-d8a3-428c-9d2e-368592e777cb
-- title:
--   W: gh apply
-- statement:
--   The W construction uses the gh apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/UnfoldingMatrixFreeCoordinate.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/UnfoldingMatrixFreeCoordinate.lean#L29-L32

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnfoldingMatrixFreeCoordinate
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

theorem PI.TwistedEisensteinNonvanishing.W.gh_apply {M N : ℕ} (f : (Fin M → E) →ₗ[E] (Fin N → E)) (v : Fin M → E) (l : Fin N) :
    f v l = ∑ m : Fin M, v m * f (eN E M m.1) l := by sorry
