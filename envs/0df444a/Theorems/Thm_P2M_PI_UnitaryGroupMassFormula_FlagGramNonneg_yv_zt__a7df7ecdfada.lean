-- Prove2me | Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_FlagGramNonneg_yv_zt__a7df7ecdfada
-- name    : P2M_PI_UnitaryGroupMassFormula_FlagGramNonneg_yv_zt__a7df7ecdfada
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:58:26.040896+00:00
-- url     : https://prove2.me/theorems/98173c09-1dfb-5140-915e-2288b284ff6b
-- title:
--   P2 M PI Unitary Group Mass Formula Flag Gram Nonneg yv zt  a7df7ecdfada: P2 M PI Unitary Group Mass Formula Flag Gram Nonneg yv zt  a7df7ecdfada
-- statement:
--   The P2 M PI Unitary Group Mass Formula Flag Gram Nonneg yv zt  a7df7ecdfada construction uses the P2 M PI Unitary Group Mass Formula Flag Gram Nonneg yv zt  a7df7ecdfada property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/SumMulCommMulVec.lean#L159-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/SumMulCommMulVec.lean#L159-L163

import Definitions.Def_Formalism_PeriodIntegrals_FlagGramNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FlagGramNonnegativity_SumMulCommMulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PI.FlagGramNonneg
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FlagGramNonneg
variable {E : Type} [Field E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
variable (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (e e' : Fin r → V) (z z' : V)

theorem P2M_PI_UnitaryGroupMassFormula_FlagGramNonneg_yv_zt__a7df7ecdfada (hA : IsUnit (amat hT e e').det) (he' : ∀ a b, hT (e' a) (e' b) = 0)
    (hez' : ∀ a, hT (e' a) z' = 0) (a : Fin r) : hT (yv hT e e' a) (zt' hT e e' z') = 0 := by sorry

alias «PI».«UnitaryGroupMassFormula».«FlagGramNonneg».«yv_zt'» := P2M_PI_UnitaryGroupMassFormula_FlagGramNonneg_yv_zt__a7df7ecdfada
