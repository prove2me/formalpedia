-- Prove2me | Theorems.Thm_PI_Dv_TIW_span_pi_eq
-- name    : PI.Dv.TIW.span_pi_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:32.454928+00:00
-- url     : https://prove2.me/theorems/85584442-2409-4db3-9536-857fa74fd077
-- title:
--   TIW: span pi eq
-- statement:
--   The TIW construction uses the span pi eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/IdxNonnegOfLe.lean#L66-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/IdxNonnegOfLe.lean#L66-L82

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxNonnegOfLe
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

theorem PI.Dv.TIW.span_pi_eq {ι : Type} [Fintype ι] [DecidableEq ι] (M : ι → Submodule (𝓞 K) V) :
    Submodule.span K ((Submodule.pi Set.univ M : Submodule (𝓞 K) (ι → V)) : Set (ι → V)) =
      Submodule.pi Set.univ (fun i => Submodule.span K (M i : Set V)) := by sorry
