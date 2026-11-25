-- Prove2me | Theorems.Thm_PI_LocFramePrimWork_DiffLoc_pow_nat
-- name    : PI.LocFramePrimWork.DiffLoc_pow_nat
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:13:50.950707+00:00
-- url     : https://prove2.me/theorems/4e2c92ee-1810-43a0-96bb-0fa299998ffa
-- title:
--   Loc Frame Prim Work: Diff Loc pow nat
-- statement:
--   The Loc Frame Prim Work construction uses the Diff Loc pow nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/DiffLoc.lean#L244-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/DiffLoc.lean#L244-L254

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_DiffLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocFramePrimWork
open NumberField IsDedekindDomain PI.LocFramePrim
open scoped TensorProduct Pointwise
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem PI.LocFramePrimWork.DiffLoc_pow_nat (k : ℕ) :
    DiffLoc_psi v (((ddE (E := E) F) ^ k : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) =
      Submodule.span (v.adicCompletionIntegers F) {sc (E := E) v (dV v)} ^ k * DiffLoc_P (E := E) v := by sorry
