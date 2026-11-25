-- Prove2me | Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_FlagGramNonneg_zt_e__5c081d0faef5
-- name    : P2M_PI_UnitaryGroupMassFormula_FlagGramNonneg_zt_e__5c081d0faef5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:25.708571+00:00
-- url     : https://prove2.me/theorems/8e27e49d-bc7c-4077-8494-bde340064883
-- title:
--   P2 M PI Unitary Group Mass Formula Flag Gram Nonneg zt e  5c081d0faef5: P2 M PI Unitary Group Mass Formula Flag Gram Nonneg zt e  5c081d0faef5
-- statement:
--   The P2 M PI Unitary Group Mass Formula Flag Gram Nonneg zt e  5c081d0faef5 construction uses the P2 M PI Unitary Group Mass Formula Flag Gram Nonneg zt e  5c081d0faef5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/SumMulCommMulVec.lean#L70-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/SumMulCommMulVec.lean#L70-L78

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

theorem P2M_PI_UnitaryGroupMassFormula_FlagGramNonneg_zt_e__5c081d0faef5 (hA : IsUnit (amat hT e e').det) (c : Fin r) : hT (zt hT e e' z) (e' c) = 0 := by sorry

alias «PI».«UnitaryGroupMassFormula».«FlagGramNonneg».«zt_e'» := P2M_PI_UnitaryGroupMassFormula_FlagGramNonneg_zt_e__5c081d0faef5
