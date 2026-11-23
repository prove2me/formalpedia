-- Prove2me | Theorems.Thm_PI_Dv_TIW_span_latPow
-- name    : PI.Dv.TIW.span_latPow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:15.09228+00:00
-- url     : https://prove2.me/theorems/f70d2a5d-ad40-4769-be8d-e59497cdd858
-- title:
--   TIW: span lat Pow
-- statement:
--   The TIW construction uses the span lat Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/MatVTransvection.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/MatVTransvection.lean#L57-L60

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxSmulSubMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MatVTransvection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem PI.Dv.TIW.span_latPow {n : Type} [Fintype n] [DecidableEq n] (M : Submodule (𝓞 K) V) :
    Submodule.span K ((latPow n M : Submodule (𝓞 K) (n → V)) : Set (n → V)) =
      Submodule.pi Set.univ fun _ : n => Submodule.span K (M : Set V) := by sorry
