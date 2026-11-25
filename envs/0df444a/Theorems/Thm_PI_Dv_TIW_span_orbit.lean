-- Prove2me | Theorems.Thm_PI_Dv_TIW_span_orbit
-- name    : PI.Dv.TIW.span_orbit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:19:12.503038+00:00
-- url     : https://prove2.me/theorems/f2ca0d80-2121-4135-a1d8-f262c226fcce
-- title:
--   TIW: span orbit
-- statement:
--   The TIW construction uses the span orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/AsAlgebraHomMemSpan.lean#L34-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/AsAlgebraHomMemSpan.lean#L34-L41

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_AsAlgebraHomMemSpan
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
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

theorem PI.Dv.TIW.span_orbit (τ : Representation K G W) (hirr : Function.Surjective τ.asAlgebraHom) (w : W) (hw : w ≠ 0) :
    Submodule.span K (Set.range fun x => τ x w) = ⊤ := by sorry
