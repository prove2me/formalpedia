-- Prove2me | Theorems.Thm_P2M_PI_ParahoricIdxZ_W_reindex_apply__499c1ad8652f
-- name    : P2M_PI_ParahoricIdxZ_W_reindex_apply__499c1ad8652f
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:56:58.334833+00:00
-- url     : https://prove2.me/theorems/a61b677e-2c86-56d3-ab6c-53104c70b081
-- title:
--   P2 M PI Parahoric Idx Z W reindex apply  499c1ad8652f: P2 M PI Parahoric Idx Z W reindex apply  499c1ad8652f
-- statement:
--   The P2 M PI Parahoric Idx Z W reindex apply  499c1ad8652f construction uses the P2 M PI Parahoric Idx Z W reindex apply  499c1ad8652f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ParahoricIndexCount/ThetaInjective.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ParahoricIndexCount/ThetaInjective.lean#L14-L18

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_ThetaInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ParahoricIdxZ PI.ParahoricIdxZ.W
variable {F : Type} [Field F] (O : Subring F) (ϖ : F)

theorem P2M_PI_ParahoricIdxZ_W_reindex_apply__499c1ad8652f {a t : ℕ} {R : Type} (A : Matrix (Fin (a + t)) (Fin (a + t)) R)
    (x y : Fin a ⊕ Fin t) :
    Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm A x y =
      A (finSumFinEquiv x) (finSumFinEquiv y) := by sorry

alias «PI».«ParahoricIdxZ».«W».«reindex_apply'» := P2M_PI_ParahoricIdxZ_W_reindex_apply__499c1ad8652f
