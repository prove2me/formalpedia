-- Prove2me | Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_FlagGramNonneg_e_zt__73625be99166
-- name    : P2M_PI_UnitaryGroupMassFormula_FlagGramNonneg_e_zt__73625be99166
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:58:41.454946+00:00
-- url     : https://prove2.me/theorems/f08d6962-e769-4776-af31-69a106980be1
-- title:
--   P2 M PI Unitary Group Mass Formula Flag Gram Nonneg e zt  73625be99166: P2 M PI Unitary Group Mass Formula Flag Gram Nonneg e zt  73625be99166
-- statement:
--   The P2 M PI Unitary Group Mass Formula Flag Gram Nonneg e zt  73625be99166 construction uses the P2 M PI Unitary Group Mass Formula Flag Gram Nonneg e zt  73625be99166 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/SumMulCommMulVec.lean#L61-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/SumMulCommMulVec.lean#L61-L68

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

theorem P2M_PI_UnitaryGroupMassFormula_FlagGramNonneg_e_zt__73625be99166 (hA : IsUnit (amat hT e e').det) (c : Fin r) : hT (e c) (zt' hT e e' z') = 0 := by sorry

alias «PI».«UnitaryGroupMassFormula».«FlagGramNonneg».«e_zt'» := P2M_PI_UnitaryGroupMassFormula_FlagGramNonneg_e_zt__73625be99166
