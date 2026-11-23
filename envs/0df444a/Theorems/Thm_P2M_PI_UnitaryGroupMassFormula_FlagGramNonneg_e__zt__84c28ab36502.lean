-- Prove2me | Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_FlagGramNonneg_e__zt__84c28ab36502
-- name    : P2M_PI_UnitaryGroupMassFormula_FlagGramNonneg_e__zt__84c28ab36502
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:20.531835+00:00
-- url     : https://prove2.me/theorems/a71178a1-25a1-46cd-b566-307de71bbbcb
-- title:
--   P2 M PI Unitary Group Mass Formula Flag Gram Nonneg e  zt  84c28ab36502: P2 M PI Unitary Group Mass Formula Flag Gram Nonneg e  zt  84c28ab36502
-- statement:
--   The P2 M PI Unitary Group Mass Formula Flag Gram Nonneg e  zt  84c28ab36502 construction uses the P2 M PI Unitary Group Mass Formula Flag Gram Nonneg e  zt  84c28ab36502 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/SumMulCommMulVec.lean#L86-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/SumMulCommMulVec.lean#L86-L90

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

theorem P2M_PI_UnitaryGroupMassFormula_FlagGramNonneg_e__zt__84c28ab36502 (he' : ∀ a b, hT (e' a) (e' b) = 0) (hez' : ∀ a, hT (e' a) z' = 0) (c : Fin r) :
    hT (e' c) (zt' hT e e' z') = 0 := by sorry

alias «PI».«UnitaryGroupMassFormula».«FlagGramNonneg».«e'_zt'» := P2M_PI_UnitaryGroupMassFormula_FlagGramNonneg_e__zt__84c28ab36502
