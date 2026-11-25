-- Prove2me | Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_FlagGramNonneg_zt_zt__91f257c1d34a
-- name    : P2M_PI_UnitaryGroupMassFormula_FlagGramNonneg_zt_zt__91f257c1d34a
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:58:27.356271+00:00
-- url     : https://prove2.me/theorems/4f6bf8b8-b842-5d06-b495-40d15b2c3400
-- title:
--   P2 M PI Unitary Group Mass Formula Flag Gram Nonneg zt zt  91f257c1d34a: P2 M PI Unitary Group Mass Formula Flag Gram Nonneg zt zt  91f257c1d34a
-- statement:
--   The P2 M PI Unitary Group Mass Formula Flag Gram Nonneg zt zt  91f257c1d34a construction uses the P2 M PI Unitary Group Mass Formula Flag Gram Nonneg zt zt  91f257c1d34a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/SumMulCommMulVec.lean#L113-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/SumMulCommMulVec.lean#L113-L121

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

theorem P2M_PI_UnitaryGroupMassFormula_FlagGramNonneg_zt_zt__91f257c1d34a (hA : IsUnit (amat hT e e').det) :
    hT (zt hT e e' z) (zt' hT e e' z') = sval hT e e' z z' := by sorry

alias «PI».«UnitaryGroupMassFormula».«FlagGramNonneg».«zt_zt'» := P2M_PI_UnitaryGroupMassFormula_FlagGramNonneg_zt_zt__91f257c1d34a
